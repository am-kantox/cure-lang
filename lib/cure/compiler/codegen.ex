defmodule Cure.Compiler.Codegen do
  @moduledoc """
  Code generator for the Cure programming language.

  Translates MetaAST 3-tuples (produced by `Cure.Compiler.Parser`) into Erlang
  abstract forms suitable for `:compile.forms/2`.

  ## Pipeline Events

  Emits via `Cure.Pipeline.Events`:

  - `{:codegen, :form_generated, form, meta}` -- after each function form
  - `{:codegen, :module_assembled, forms, meta}` -- after full module assembly
  - `{:codegen, :error, error, meta}` -- on codegen errors

  ## Usage

      {:ok, ast} = Cure.Compiler.Parser.parse(tokens)
      {:ok, forms} = Cure.Compiler.Codegen.compile_module(ast)
  """

  alias Cure.Pipeline.Events
  alias Cure.FSM.{Compiler, Verifier}
  alias Cure.Types.{Protocol, ProtocolRegistry}

  # -- Codegen State -----------------------------------------------------------

  defstruct [
    :module_name,
    line: 1,
    vars: %{},
    exports: [],
    imports: [],
    temp_counter: 0,
    emit_events: true,
    file: "nofile"
  ]

  @type t :: %__MODULE__{}

  # -- Public API --------------------------------------------------------------

  @doc """
  Compile a module MetaAST node into Erlang abstract forms.

  Expects a `{:container, [container_type: :module, ...], body}` node.
  Returns `{:ok, forms}` where `forms` is a list of Erlang abstract forms
  ready for `:compile.forms/2`.
  """
  @spec compile_module(tuple(), keyword()) :: {:ok, list()} | {:error, term()}
  def compile_module(ast, opts \\ []) do
    emit? = Keyword.get(opts, :emit_events, true)
    file = Keyword.get(opts, :file, "nofile")

    case ast do
      {:container, meta, body} when is_list(meta) ->
        dispatch_container(meta, body, emit?, file)

      # If the AST is a block, find the first container (module/fsm) inside it
      # and merge any sibling definitions into its body (the parser may place
      # function definitions in a sibling block rather than inside the container).
      {:block, _, children} when is_list(children) ->
        case find_container(children) do
          {:container, meta, body} ->
            merged_body = merge_sibling_defs(body, children)
            dispatch_container(meta, merged_body, emit?, file)

          nil ->
            {:error, {:expected_module, ast}}
        end

      _ ->
        {:error, {:expected_module, ast}}
    end
  end

  @doc """
  Compile a single expression MetaAST node into an Erlang abstract form.

  Useful for testing and REPL scenarios.
  """
  @spec compile_expr(tuple()) :: {:ok, tuple()}
  def compile_expr(ast) do
    state = %__MODULE__{}
    {form, _state} = do_compile_expr(ast, state)
    {:ok, form}
  end

  # -- Container Dispatch ------------------------------------------------------

  defp dispatch_container(meta, body, emit?, file) do
    case Keyword.get(meta, :container_type) do
      :module ->
        compile_module_container(meta, body, emit?, file)

      :fsm ->
        ast = {:container, meta, body}
        # Run verification first
        _ = Verifier.verify(ast, emit_events: emit?, file: file)
        # Compile to gen_statem
        Compiler.compile(ast, emit_events: emit?, file: file)

      other ->
        {:error, {:unsupported_container, other}}
    end
  end

  # -- Module Compilation ------------------------------------------------------

  defp compile_module_container(meta, body, emit?, file) do
    name = Keyword.get(meta, :name, "Unnamed")
    module_atom = cure_module_to_atom(name)

    state = %__MODULE__{
      module_name: module_atom,
      emit_events: emit?,
      file: file
    }

    # Collect function definitions and build export list
    {fn_forms, state} = compile_module_body(body, state)

    # Module attribute forms
    mod_attr = {:attribute, 1, :module, module_atom}
    export_attr = {:attribute, 2, :export, state.exports}

    # Suppress errors for functions that shadow auto-imported BIFs (OTP 27+)
    no_auto_import_attr = build_no_auto_import_attr(fn_forms)

    forms = [mod_attr, export_attr] ++ no_auto_import_attr ++ fn_forms

    if emit? do
      Events.emit(:codegen, :module_assembled, forms, Events.meta(file, 1))
    end

    {:ok, forms}
  end

  defp compile_module_body(stmts, state) do
    # Phase 0a: pre-collect all local function names for import priority
    local_fns = collect_local_fn_names(stmts)

    # Phase 0b: collect imports (store local_fns via a temporary field)
    state = collect_imports(stmts, state)
    # Store local_fns so import resolver can check them
    state = Map.put(state, :local_fns, local_fns)

    # Phase 1: collect protocol and impl definitions
    proto_ctx = collect_protocol_context(stmts)

    # Phase 2: generate impl functions (private) and dispatch functions (exported)
    {proto_forms, state} = compile_protocol_dispatch(proto_ctx, state)

    # Phase 2b: register impls in the global protocol registry
    register_impls_globally(proto_ctx, state.module_name)

    # Phase 3: compile regular function definitions
    {fn_forms, state} =
      Enum.reduce(stmts, {[], state}, fn stmt, {forms_acc, st} ->
        case stmt do
          {:function_def, meta, body} ->
            {form, st} = compile_function_def(meta, body, st)
            {forms_acc ++ [form], st}

          {:import, _meta, _children} ->
            {forms_acc, st}

          {:container, _meta, _body} ->
            # Protocol/impl/nested containers handled in phase 1-2
            {forms_acc, st}

          _ ->
            {forms_acc, st}
        end
      end)

    {proto_forms ++ fn_forms, state}
  end

  # -- Auto-Import Suppression -------------------------------------------------

  defp build_no_auto_import_attr(fn_forms) do
    shadowed =
      fn_forms
      |> Enum.flat_map(fn
        {:function, _line, name, arity, _clauses} ->
          if :erl_internal.bif(name, arity), do: [{name, arity}], else: []

        _ ->
          []
      end)
      |> Enum.uniq()

    case shadowed do
      [] -> []
      bifs -> [{:attribute, 1, :compile, {:no_auto_import, bifs}}]
    end
  end

  # -- Import Collection -------------------------------------------------------

  defp collect_imports(stmts, state) do
    import_modules =
      Enum.flat_map(stmts, fn
        {:import, meta, _} ->
          source = Keyword.get(meta, :source, "")
          items = Keyword.get(meta, :items, [])

          if items == [] do
            # use Std.List -> import from std_list
            [cure_module_to_atom(source)]
          else
            # use Std.{List, Core} -> import from std_list, std_core
            Enum.map(items, fn item -> cure_module_to_atom(source <> "." <> item) end)
          end

        _ ->
          []
      end)

    %{state | imports: import_modules}
  end

  defp collect_local_fn_names(stmts) do
    Enum.flat_map(stmts, fn
      {:function_def, meta, _} ->
        name = Keyword.get(meta, :name, "unknown")
        params = Keyword.get(meta, :params, [])
        [{mangle_fn_name(name), length(params)}]

      _ ->
        []
    end)
  end

  # -- Protocol Registry --------------------------------------------------------

  defp register_impls_globally(%Protocol{protocols: protos} = ctx, module_atom) do
    Enum.each(protos, fn {proto_name, proto_def} ->
      impls = Protocol.impls_for(ctx, proto_name)

      Enum.each(impls, fn impl ->
        Enum.each(proto_def.methods, fn method_sig ->
          ProtocolRegistry.register_impl(
            proto_name,
            method_sig.name,
            impl.for_type,
            module_atom
          )
        end)
      end)
    end)
  end

  # -- Protocol / Impl Collection and Compilation

  defp collect_protocol_context(stmts) do
    Enum.reduce(stmts, Protocol.new(), fn stmt, ctx ->
      case stmt do
        {:container, meta, body} when is_list(meta) ->
          case Keyword.get(meta, :container_type) do
            :protocol -> Protocol.register_protocol(ctx, meta, body)
            :trait -> Protocol.register_impl(ctx, meta, body)
            _ -> ctx
          end

        _ ->
          ctx
      end
    end)
  end

  defp compile_protocol_dispatch(%Protocol{protocols: protos} = _ctx, state) when map_size(protos) == 0 do
    # No protocols -> nothing to generate
    {[], state}
  end

  defp compile_protocol_dispatch(%Protocol{} = ctx, state) do
    Enum.reduce(ctx.protocols, {[], state}, fn {proto_name, proto_def}, {forms_acc, st} ->
      impls = Protocol.impls_for(ctx, proto_name)

      # For each method in the protocol, generate impl fns + dispatch fn
      {method_forms, st} =
        Enum.reduce(proto_def.methods, {[], st}, fn method_sig, {mf_acc, st2} ->
          {impl_forms, dispatch_form, st2} =
            compile_method_dispatch(method_sig, impls, st2)

          {mf_acc ++ impl_forms ++ [dispatch_form], st2}
        end)

      {forms_acc ++ method_forms, st}
    end)
  end

  defp compile_method_dispatch(method_sig, impls, state) do
    method_name = method_sig.name
    params = method_sig.params
    arity = length(params)
    line = 1

    # Sort impls by type specificity (Bool before Atom, etc.)
    sorted_impls = Enum.sort_by(impls, &Protocol.type_specificity(&1.for_type))

    # Generate one private function per impl
    {impl_forms, dispatch_clauses, state} =
      Enum.reduce(sorted_impls, {[], [], state}, fn impl, {if_acc, dc_acc, st} ->
        for_type = impl.for_type

        # Find the matching method body in this impl
        method_ast =
          Enum.find(impl.methods, fn
            {:function_def, m, _} -> Keyword.get(m, :name) == method_name
            _ -> false
          end)

        case method_ast do
          {:function_def, meta, body} ->
            # Compile the impl method as a private function with mangled name
            mangled = Protocol.mangle_impl_name(method_name, for_type)
            impl_meta = Keyword.put(meta, :visibility, :private)

            {impl_form, st} = compile_function_def(impl_meta, body, st)

            # Rename the function to the mangled name and fix arity
            impl_form = rename_function(impl_form, mangled)

            # Build dispatch clause: when is_type(FirstArg) -> mangled(args)
            {dc, st} = build_dispatch_clause(mangled, for_type, arity, line, st)

            {if_acc ++ [impl_form], dc_acc ++ [dc], st}

          _ ->
            {if_acc, dc_acc, st}
        end
      end)

    # Build the dispatch function from all clauses
    dispatch_name = mangle_fn_name(method_name)
    state = %{state | exports: [{dispatch_name, arity} | state.exports]}
    dispatch_form = {:function, line, dispatch_name, arity, dispatch_clauses}

    {impl_forms, dispatch_form, state}
  end

  defp build_dispatch_clause(mangled_name, for_type, arity, line, state) do
    # Build parameter variables
    param_vars =
      Enum.map(0..(arity - 1), fn i ->
        {:var, line, String.to_atom("V_arg#{i}")}
      end)

    # First param is the dispatched-on argument
    first_var = hd(param_vars)

    # Guard based on the type
    guard = Protocol.type_guard(first_var, for_type, line)

    guard_forms = [[guard]]

    # Body: call the mangled impl function with the same args
    body = [{:call, line, {:atom, line, mangled_name}, param_vars}]

    clause = {:clause, line, param_vars, guard_forms, body}
    {clause, state}
  end

  defp rename_function({:function, line, _old_name, arity, clauses}, new_name) do
    {:function, line, new_name, arity, clauses}
  end

  # -- Function Definition Compilation ----------------------------------------

  defp compile_function_def(meta, body, state) do
    name = Keyword.get(meta, :name, "unknown")
    fn_atom = mangle_fn_name(name)
    params = Keyword.get(meta, :params, [])
    arity = Keyword.get(meta, :arity, length(params))
    visibility = Keyword.get(meta, :visibility, :public)
    line = Keyword.get(meta, :line, 1)
    extern = Keyword.get(meta, :extern)
    clauses_meta = Keyword.get(meta, :clauses)

    # Update exports
    state =
      if visibility == :public do
        %{state | exports: [{fn_atom, arity} | state.exports]}
      else
        state
      end

    form =
      cond do
        # @extern function: generate wrapper delegating to remote call
        extern != nil ->
          compile_extern_function(fn_atom, params, extern, line, state)

        # Multi-clause function
        clauses_meta != nil ->
          compile_multi_clause_function(fn_atom, arity, clauses_meta, line, state)

        # Regular function with body
        true ->
          guard_ast = Keyword.get(meta, :guards)
          compile_regular_function(fn_atom, params, body, guard_ast, line, state)
      end

    if state.emit_events do
      Events.emit(:codegen, :form_generated, form, Events.meta(state.file, line))
    end

    {form, state}
  end

  defp compile_regular_function(fn_atom, params, body, guard_ast, line, state) do
    # Build param vars and populate scope
    {param_forms, fn_state} = build_param_forms(params, line, state)

    # Compile guard if present
    guard_forms = compile_guard(guard_ast, fn_state)

    # Compile body
    body_forms =
      case body do
        [single] ->
          {form, _st} = do_compile_expr(single, fn_state)
          [form]

        [] ->
          [{:atom, line, :ok}]

        multiple ->
          compile_body_exprs(multiple, fn_state)
      end

    clause = {:clause, line, param_forms, guard_forms, body_forms}
    {:function, line, fn_atom, length(params), [clause]}
  end

  defp compile_extern_function(fn_atom, params, extern, line, state) do
    {ext_mod, ext_fun, _ext_arity} =
      case extern do
        {m, f, a} -> {m, f, a}
        _ -> {:erlang, :error, length(params)}
      end

    {param_forms, _fn_state} = build_param_forms(params, line, state)

    remote_call =
      {:call, line, {:remote, line, {:atom, line, ext_mod}, {:atom, line, ext_fun}}, param_forms}

    clause = {:clause, line, param_forms, [], [remote_call]}
    {:function, line, fn_atom, length(params), [clause]}
  end

  defp compile_multi_clause_function(fn_atom, arity, clauses, line, state) do
    erl_clauses =
      Enum.map(clauses, fn %{params: params, guard: guard, body: body_list} ->
        # Each clause has its own scope
        clause_state = %{state | vars: %{}}

        {pattern_forms, clause_state} =
          Enum.map_reduce(params, clause_state, fn pat, st ->
            compile_pattern(pat, st)
          end)

        guard_forms = compile_guard(guard, clause_state)

        body_forms = compile_body_exprs(body_list, clause_state)

        {:clause, line, pattern_forms, guard_forms, body_forms}
      end)

    {:function, line, fn_atom, arity, erl_clauses}
  end

  # -- Expression Compilation --------------------------------------------------

  defp do_compile_expr(ast, state) do
    case ast do
      # Literals
      {:literal, meta, value} ->
        compile_literal(meta, value, state)

      # Variables
      {:variable, _meta, name} ->
        compile_variable(name, state)

      # Binary operators
      {:binary_op, meta, [left, right]} ->
        compile_binary_op(meta, left, right, state)

      # Unary operators
      {:unary_op, meta, [operand]} ->
        compile_unary_op(meta, operand, state)

      # Function calls
      {:function_call, meta, args} ->
        compile_function_call(meta, args, state)

      # Let binding (assignment)
      {:assignment, meta, [pattern, value]} ->
        compile_assignment(meta, pattern, value, state)

      # Augmented assignment
      {:augmented_assignment, meta, [var_ast, value]} ->
        compile_augmented_assignment(meta, var_ast, value, state)

      # Conditional
      {:conditional, meta, [condition, then_branch, else_branch]} ->
        compile_conditional(meta, condition, then_branch, else_branch, state)

      # Pattern match
      {:pattern_match, meta, [scrutinee | arms]} ->
        compile_pattern_match(meta, scrutinee, arms, state)

      # Block
      {:block, _meta, exprs} ->
        compile_block(exprs, state)

      # Collections
      {:list, meta, elems} ->
        compile_list(meta, elems, state)

      {:tuple, meta, elems} ->
        compile_tuple(meta, elems, state)

      {:map, meta, pairs} ->
        compile_map(meta, pairs, state)

      # Lambda
      {:lambda, meta, [body]} ->
        compile_lambda(meta, body, state)

      # String interpolation
      {:string_interpolation, meta, parts} ->
        compile_string_interpolation(meta, parts, state)

      # Attribute access (obj.field)
      {:attribute_access, meta, [obj]} ->
        compile_attribute_access(meta, obj, state)

      # Range
      {:range, meta, [from, to]} ->
        compile_range(meta, from, to, state)

      # Early return
      {:early_return, meta, [expr]} ->
        compile_early_return(meta, expr, state)

      # Throw
      {:throw, meta, [expr]} ->
        compile_throw(meta, expr, state)

      # Comprehension
      {:comprehension, meta, children} ->
        compile_comprehension(meta, children, state)

      # Exception handling
      {:exception_handling, meta, children} ->
        compile_try(meta, children, state)

      # Record update: TypeName{base | field: val, ...}
      {:record_update, meta, [base | fields]} ->
        compile_record_update(meta, base, fields, state)

      # Containers in expression position (nested modules, etc.)
      # Compile the nested container as a side effect and return the module atom.
      {:container, meta, body} when is_list(meta) ->
        line = Keyword.get(meta, :line, 1)

        case dispatch_container(meta, body, state.emit_events, state.file) do
          {:ok, forms} ->
            # Load the module into the VM at compile time
            case Cure.Compiler.BeamWriter.compile_and_load(forms) do
              {:ok, mod_atom} ->
                {{:atom, line, mod_atom}, state}

              {:error, _} ->
                {{:atom, line, :undefined}, state}
            end

          {:error, _} ->
            {{:atom, line, :undefined}, state}
        end

      # Param nodes in pattern position
      {:param, _meta, _name} ->
        # Handled by compile_pattern
        {{:atom, 1, :ok}, state}

      # Fallback -- emit a warning so unrecognized nodes are visible
      other ->
        line = extract_ast_line(other)
        tag = if is_tuple(other) and tuple_size(other) >= 1, do: elem(other, 0), else: :unknown

        if state.emit_events do
          Events.emit(
            :codegen,
            :warning,
            {:unrecognized_node, "unrecognized AST node '#{tag}' compiled as :undefined", line: line},
            Events.meta(state.file, line)
          )
        end

        {{:atom, line, :undefined}, state}
    end
  end

  defp extract_ast_line(ast) when is_tuple(ast) and tuple_size(ast) >= 2 do
    case elem(ast, 1) do
      meta when is_list(meta) -> Keyword.get(meta, :line, 1)
      _ -> 1
    end
  end

  defp extract_ast_line(_), do: 1

  # -- Literal Compilation -----------------------------------------------------

  defp compile_literal(meta, value, state) do
    line = Keyword.get(meta, :line, state.line)
    subtype = Keyword.get(meta, :subtype)

    form =
      case subtype do
        :integer -> {:integer, line, value}
        :float -> {:float, line, value}
        :string -> compile_string_literal(value, line)
        :boolean -> {:atom, line, value}
        :null -> {:atom, line, nil}
        :symbol -> {:atom, line, value}
        :char -> {:integer, line, value}
        :regex -> compile_regex_literal(value, line)
        :bytes -> compile_bytes_literal(value, line)
        _ -> {:atom, line, value}
      end

    {form, state}
  end

  defp compile_string_literal(value, line) when is_binary(value) do
    {:bin, line, [{:bin_element, line, {:string, line, String.to_charlist(value)}, :default, [:utf8]}]}
  end

  defp compile_string_literal(value, line) do
    {:atom, line, value}
  end

  defp compile_regex_literal({pattern, flags}, line) do
    # Compile regex as a call to re:compile/2
    {:call, line, {:remote, line, {:atom, line, :re}, {:atom, line, :compile}},
     [
       {:bin, line, [{:bin_element, line, {:string, line, String.to_charlist(pattern)}, :default, [:utf8]}]},
       compile_regex_flags(flags, line)
     ]}
  end

  defp compile_regex_literal(_, line) do
    {:atom, line, :undefined}
  end

  defp compile_regex_flags(flags, line) when is_binary(flags) do
    opts =
      flags
      |> String.graphemes()
      |> Enum.map(fn
        "i" -> {:atom, line, :caseless}
        "m" -> {:atom, line, :multiline}
        "s" -> {:atom, line, :dotall}
        "x" -> {:atom, line, :extended}
        _ -> nil
      end)
      |> Enum.reject(&is_nil/1)

    case opts do
      [] -> {nil, line}
      _ -> build_list(opts, line)
    end
  end

  defp compile_regex_flags(_, line), do: {nil, line}

  defp compile_bytes_literal(value, line) when is_binary(value) do
    # Compile binary byte string as an Erlang binary literal (raw bytes, no utf8 annotation)
    {:bin, line, [{:bin_element, line, {:string, line, :binary.bin_to_list(value)}, :default, :default}]}
  end

  defp compile_bytes_literal(value, line) when is_list(value) do
    # List of byte integers -> binary with one element per byte
    elements =
      Enum.map(value, fn byte ->
        {:bin_element, line, {:integer, line, byte}, :default, :default}
      end)

    {:bin, line, elements}
  end

  defp compile_bytes_literal(_value, line) do
    # Unknown format -- produce empty binary
    {:bin, line, []}
  end

  # -- Variable Compilation ----------------------------------------------------

  defp compile_variable(name, state) do
    line = state.line
    var_atom = mangle_var(name)
    form = {:var, line, var_atom}
    {form, state}
  end

  # -- Binary Operator Compilation ---------------------------------------------

  defp compile_binary_op(meta, left, right, state) do
    line = Keyword.get(meta, :line, state.line)
    op = Keyword.get(meta, :operator)

    {left_form, state} = do_compile_expr(left, state)
    {right_form, state} = do_compile_expr(right, state)

    form =
      case op do
        :<> ->
          # String concatenation: erlang:iolist_to_binary([left, right])
          list_form = {:cons, line, left_form, {:cons, line, right_form, {nil, line}}}

          {:call, line, {:remote, line, {:atom, line, :erlang}, {:atom, line, :iolist_to_binary}}, [list_form]}

        _ ->
          erl_op = cure_op_to_erlang(op)
          {:op, line, erl_op, left_form, right_form}
      end

    {form, state}
  end

  # -- Unary Operator Compilation ----------------------------------------------

  defp compile_unary_op(meta, operand, state) do
    line = Keyword.get(meta, :line, state.line)
    op = Keyword.get(meta, :operator)
    {operand_form, state} = do_compile_expr(operand, state)
    erl_op = cure_op_to_erlang(op)
    form = {:op, line, erl_op, operand_form}
    {form, state}
  end

  # -- Function Call Compilation -----------------------------------------------

  defp compile_function_call(meta, args, state) do
    line = Keyword.get(meta, :line, state.line)
    name = Keyword.get(meta, :name, "unknown")
    is_record = Keyword.get(meta, :record, false)

    # Record field pairs must be compiled as map_field_assoc forms, not as
    # plain expressions.  The {:pair, ...} MetaAST node has no handler in
    # do_compile_expr and would fall through to the :undefined fallback.
    if is_record do
      {field_forms, state} =
        Enum.map_reduce(args, state, fn pair, st ->
          case pair do
            {:pair, _, [key, value]} ->
              {k_form, st} = do_compile_expr(key, st)
              {v_form, st} = do_compile_expr(value, st)
              {{:map_field_assoc, line, k_form, v_form}, st}

            _ ->
              {form, st} = do_compile_expr(pair, st)
              {form, st}
          end
        end)

      form = compile_record_construction(name, field_forms, line)
      {form, state}
    else
      {arg_forms, state} =
        Enum.map_reduce(args, state, fn arg, st ->
          do_compile_expr(arg, st)
        end)

      form =
        cond do
          # Record construction handled above; this branch is unreachable when is_record.
          is_record ->
            compile_record_construction(name, arg_forms, line)

          # Qualified call: Mod.fun(args) -- must come before constructor check
          String.contains?(name, ".") ->
            compile_qualified_call(name, arg_forms, line)

          # ADT constructor: PascalCase name -> tagged tuple
          constructor?(name) ->
            compile_constructor_call(name, arg_forms, line)

          # Variable call: if the name is a variable in scope, call it as a function value
          Map.has_key?(state.vars, name) ->
            var_atom = mangle_var(name)
            {:call, line, {:var, line, var_atom}, arg_forms}

          # Expression call: callee is an arbitrary expression (e.g. f(x)(y))
          Keyword.has_key?(meta, :callee) ->
            callee = Keyword.get(meta, :callee)
            {callee_form, _st} = do_compile_expr(callee, state)
            {:call, line, callee_form, arg_forms}

          # Import resolution: check imports only if NOT a locally defined function
          true ->
            fn_atom = mangle_fn_name(name)
            arity = length(arg_forms)
            local_fns = Map.get(state, :local_fns, [])
            is_local = Enum.any?(state.exports ++ local_fns, fn {n, a} -> n == fn_atom and a == arity end)

            if is_local or state.imports == [] do
              {:call, line, {:atom, line, fn_atom}, arg_forms}
            else
              case resolve_import(fn_atom, arity, state.imports) do
                {:ok, mod_atom} ->
                  {:call, line, {:remote, line, {:atom, line, mod_atom}, {:atom, line, fn_atom}}, arg_forms}

                :not_found ->
                  # Last resort: check protocol registry for cross-module dispatch
                  case resolve_protocol_call(name, arity, line) do
                    {:ok, form} -> form
                    :not_found -> {:call, line, {:atom, line, fn_atom}, arg_forms}
                  end
              end
            end
        end

      {form, state}
    end
  end

  defp compile_qualified_call(name, arg_forms, line) do
    parts = String.split(name, ".")
    {mod_parts, [fun_name]} = Enum.split(parts, -1)
    mod_atom = cure_module_to_atom(Enum.join(mod_parts, "."))
    fun_atom = mangle_fn_name(fun_name)

    {:call, line, {:remote, line, {:atom, line, mod_atom}, {:atom, line, fun_atom}}, arg_forms}
  end

  defp compile_constructor_call(name, arg_forms, line) do
    tag = constructor_tag(name)
    {:tuple, line, [{:atom, line, tag} | arg_forms]}
  end

  # -- Record Update Compilation -----------------------------------------------

  defp compile_record_update(meta, base_ast, field_pairs, state) do
    line = Keyword.get(meta, :line, state.line)
    {base_form, state} = do_compile_expr(base_ast, state)

    {exact_forms, state} =
      Enum.map_reduce(field_pairs, state, fn
        {:pair, _, [key, value]}, st ->
          {k_form, st} = do_compile_expr(key, st)
          {v_form, st} = do_compile_expr(value, st)
          # map_field_exact compiles to Map#{key := value}, which requires the
          # key to already exist.  This is the correct semantics for record update.
          {{:map_field_exact, line, k_form, v_form}, st}

        other, st ->
          {form, st} = do_compile_expr(other, st)
          {form, st}
      end)

    # {:map, Line, BaseExpr, [ExactPairs]} is Erlang abstract-format for Map#{...}
    form = {:map, line, base_form, exact_forms}
    {form, state}
  end

  defp compile_record_construction(name, pair_forms, line) do
    struct_tag =
      {:map_field_assoc, line, {:atom, line, :__struct__}, {:atom, line, constructor_tag(name)}}

    field_assocs =
      Enum.map(pair_forms, fn
        {:pair, _, [{:literal, [subtype: :symbol], key}, value_form]} ->
          {:map_field_assoc, line, {:atom, line, key}, value_form}

        {:tuple, _, [{:atom, _, key}, value_form]} ->
          {:map_field_assoc, line, {:atom, line, key}, value_form}

        # Already a map_field_assoc from compilation
        {:map_field_assoc, _, _, _} = assoc ->
          assoc

        other ->
          other
      end)

    {:map, line, [struct_tag | field_assocs]}
  end

  # -- Assignment (let binding) ------------------------------------------------

  defp compile_assignment(meta, pattern, value, state) do
    line = Keyword.get(meta, :line, state.line)
    {val_form, state} = do_compile_expr(value, state)
    {pat_form, state} = compile_pattern(pattern, state)

    form = {:match, line, pat_form, val_form}
    {form, state}
  end

  # -- Augmented Assignment ----------------------------------------------------

  defp compile_augmented_assignment(meta, var_ast, value, state) do
    line = Keyword.get(meta, :line, state.line)
    op = Keyword.get(meta, :operator)

    {var_form, state} = do_compile_expr(var_ast, state)
    {val_form, state} = do_compile_expr(value, state)

    erl_op = cure_op_to_erlang(op)
    rhs = {:op, line, erl_op, var_form, val_form}
    form = {:match, line, var_form, rhs}
    {form, state}
  end

  # -- Conditional (if/elif/else) ----------------------------------------------

  defp compile_conditional(meta, condition, then_branch, else_branch, state) do
    line = Keyword.get(meta, :line, state.line)

    {cond_form, state} = do_compile_expr(condition, state)
    {then_form, state} = do_compile_expr(then_branch, state)
    {else_form, state} = do_compile_expr(else_branch, state)

    form =
      {:case, line, cond_form,
       [
         {:clause, line, [{:atom, line, true}], [], [then_form]},
         {:clause, line, [{:atom, line, false}], [], [else_form]}
       ]}

    {form, state}
  end

  # -- Pattern Match (match expr) ----------------------------------------------

  defp compile_pattern_match(meta, scrutinee, arms, state) do
    line = Keyword.get(meta, :line, state.line)
    {scrutinee_form, state} = do_compile_expr(scrutinee, state)

    {clauses, state} =
      Enum.map_reduce(arms, state, fn {:match_arm, arm_meta, [body]}, st ->
        pattern = Keyword.get(arm_meta, :pattern)
        guard = Keyword.get(arm_meta, :guard)

        # Each arm gets its own scope for pattern variables
        arm_state = st
        {pat_form, arm_state} = compile_pattern(pattern, arm_state)
        guard_forms = compile_guard(guard, arm_state)
        {body_form, _arm_state} = do_compile_expr(body, arm_state)

        clause = {:clause, line, [pat_form], guard_forms, [body_form]}
        {clause, st}
      end)

    form = {:case, line, scrutinee_form, clauses}
    {form, state}
  end

  # -- Block -------------------------------------------------------------------

  defp compile_block(exprs, state) do
    body_forms = compile_body_exprs(exprs, state)

    case body_forms do
      [single] ->
        {single, state}

      multiple ->
        # Erlang block expression
        line = state.line
        form = {:block, line, multiple}
        {form, state}
    end
  end

  defp compile_body_exprs(exprs, state) do
    {forms, _st} =
      Enum.map_reduce(exprs, state, fn expr, st ->
        do_compile_expr(expr, st)
      end)

    case forms do
      [] -> [{:atom, state.line, :ok}]
      _ -> forms
    end
  end

  # -- List Compilation --------------------------------------------------------

  defp compile_list(meta, elems, state) do
    line = Keyword.get(meta, :line, state.line)
    is_cons = Keyword.get(meta, :cons, false)

    if is_cons do
      # [h | t] -> {:cons, L, h, t}
      case elems do
        [head, tail] ->
          {h_form, state} = do_compile_expr(head, state)
          {t_form, state} = do_compile_expr(tail, state)
          {{:cons, line, h_form, t_form}, state}

        _ ->
          # Shouldn't happen, but handle gracefully
          compile_regular_list(elems, line, state)
      end
    else
      compile_regular_list(elems, line, state)
    end
  end

  defp compile_regular_list(elems, line, state) do
    {elem_forms, state} =
      Enum.map_reduce(elems, state, fn elem, st ->
        do_compile_expr(elem, st)
      end)

    form = build_cons_list(elem_forms, line)
    {form, state}
  end

  defp build_cons_list([], line), do: {nil, line}

  defp build_cons_list([h | t], line) do
    {:cons, line, h, build_cons_list(t, line)}
  end

  # -- Tuple Compilation -------------------------------------------------------

  defp compile_tuple(meta, elems, state) do
    line = Keyword.get(meta, :line, state.line)

    {elem_forms, state} =
      Enum.map_reduce(elems, state, fn elem, st ->
        do_compile_expr(elem, st)
      end)

    {{:tuple, line, elem_forms}, state}
  end

  # -- Map Compilation ---------------------------------------------------------

  defp compile_map(meta, pairs, state) do
    line = Keyword.get(meta, :line, state.line)

    {field_forms, state} =
      Enum.map_reduce(pairs, state, fn {:pair, _, [key, value]}, st ->
        {k_form, st} = do_compile_expr(key, st)
        {v_form, st} = do_compile_expr(value, st)
        {{:map_field_assoc, line, k_form, v_form}, st}
      end)

    {{:map, line, field_forms}, state}
  end

  # -- Lambda Compilation ------------------------------------------------------

  defp compile_lambda(meta, body, state) do
    line = Keyword.get(meta, :line, state.line)
    params = Keyword.get(meta, :params, [])

    # Lambdas inherit the enclosing scope so closures can capture outer variables
    lambda_state = state

    {param_forms, lambda_state} =
      Enum.map_reduce(params, lambda_state, fn {:param, _, name}, st ->
        var_atom = mangle_var(name)
        st = %{st | vars: Map.put(st.vars, name, var_atom)}
        {{:var, line, var_atom}, st}
      end)

    {body_form, _lambda_state} = do_compile_expr(body, lambda_state)

    form =
      {:fun, line, {:clauses, [{:clause, line, param_forms, [], [body_form]}]}}

    {form, state}
  end

  # -- String Interpolation ----------------------------------------------------

  defp compile_string_interpolation(meta, parts, state) do
    line = Keyword.get(meta, :line, state.line)

    {part_forms, state} =
      Enum.map_reduce(parts, state, fn part, st ->
        case part do
          {:literal, [subtype: :string], s} ->
            {compile_string_literal(s, line), st}

          other ->
            # Expression part -- compile and convert to binary
            {form, st} = do_compile_expr(other, st)
            # Wrap non-string expressions in a conversion helper
            wrapped = wrap_to_iodata(form, line)
            {wrapped, st}
        end
      end)

    # Build iolist and call erlang:iolist_to_binary/1
    iolist = build_cons_list(part_forms, line)

    form =
      {:call, line, {:remote, line, {:atom, line, :erlang}, {:atom, line, :iolist_to_binary}}, [iolist]}

    {form, state}
  end

  defp wrap_to_iodata(form, line) do
    # Wrap an expression in a type-test cascade that converts any term to iodata.
    # case V of
    #   V when is_binary(V) -> V;
    #   V when is_integer(V) -> erlang:integer_to_binary(V);
    #   V when is_float(V) -> erlang:float_to_binary(V);
    #   V when is_atom(V) -> erlang:atom_to_binary(V);
    #   V -> io_lib:format("~p", [V])
    # end
    temp = {:var, line, :V__interp}

    make_guard = fn guard_fn ->
      [[{:call, line, {:atom, line, guard_fn}, [temp]}]]
    end

    make_convert = fn mod, fun ->
      {:call, line, {:remote, line, {:atom, line, mod}, {:atom, line, fun}}, [temp]}
    end

    clauses = [
      {:clause, line, [temp], make_guard.(:is_binary), [temp]},
      {:clause, line, [temp], make_guard.(:is_integer), [make_convert.(:erlang, :integer_to_binary)]},
      {:clause, line, [temp], make_guard.(:is_float), [make_convert.(:erlang, :float_to_binary)]},
      {:clause, line, [temp], make_guard.(:is_atom), [make_convert.(:erlang, :atom_to_binary)]},
      {:clause, line, [temp], [],
       [
         {:call, line, {:remote, line, {:atom, line, :erlang}, {:atom, line, :iolist_to_binary}},
          [
            {:call, line, {:remote, line, {:atom, line, :io_lib}, {:atom, line, :format}},
             [
               {:string, line, ~c"~p"},
               {:cons, line, temp, {nil, line}}
             ]}
          ]}
       ]}
    ]

    {:case, line, form, clauses}
  end

  # -- Attribute Access (obj.field) --------------------------------------------

  defp compile_attribute_access(meta, obj, state) do
    line = Keyword.get(meta, :line, state.line)
    field = Keyword.get(meta, :attribute, "unknown")
    field_atom = String.to_atom(field)

    {obj_form, state} = do_compile_expr(obj, state)

    form =
      {:call, line, {:remote, line, {:atom, line, :maps}, {:atom, line, :get}}, [{:atom, line, field_atom}, obj_form]}

    {form, state}
  end

  # -- Range -------------------------------------------------------------------

  defp compile_range(meta, from_ast, to_ast, state) do
    line = Keyword.get(meta, :line, state.line)
    inclusive = Keyword.get(meta, :inclusive, false)

    {from_form, state} = do_compile_expr(from_ast, state)
    {to_form, state} = do_compile_expr(to_ast, state)

    # Generate a list comprehension: [X || X <- lists:seq(From, To)]
    # For exclusive range: lists:seq(From, To - 1)
    end_form =
      if inclusive do
        to_form
      else
        {:op, line, :-, to_form, {:integer, line, 1}}
      end

    form =
      {:call, line, {:remote, line, {:atom, line, :lists}, {:atom, line, :seq}}, [from_form, end_form]}

    {form, state}
  end

  # -- Early Return ------------------------------------------------------------

  defp compile_early_return(meta, expr, state) do
    line = Keyword.get(meta, :line, state.line)
    {expr_form, state} = do_compile_expr(expr, state)

    form =
      {:call, line, {:atom, line, :throw}, [{:tuple, line, [{:atom, line, :cure_return}, expr_form]}]}

    {form, state}
  end

  # -- Throw -------------------------------------------------------------------

  defp compile_throw(meta, expr, state) do
    line = Keyword.get(meta, :line, state.line)
    {expr_form, state} = do_compile_expr(expr, state)

    form =
      {:call, line, {:remote, line, {:atom, line, :erlang}, {:atom, line, :throw}}, [expr_form]}

    {form, state}
  end

  # -- Comprehension -----------------------------------------------------------

  defp compile_comprehension(meta, children, state) do
    line = Keyword.get(meta, :line, state.line)

    [body | qualifiers] = children
    {body_form, state} = do_compile_expr(body, state)

    {qualifier_forms, state} =
      Enum.map_reduce(qualifiers, state, fn
        {:generator, _, [pattern, collection]}, st ->
          {pat_form, st} = compile_pattern(pattern, st)
          {coll_form, st} = do_compile_expr(collection, st)
          {{:generate, line, pat_form, coll_form}, st}

        {:filter, _, [expr]}, st ->
          {expr_form, st} = do_compile_expr(expr, st)
          {expr_form, st}
      end)

    form = {:lc, line, body_form, qualifier_forms}
    {form, state}
  end

  # -- Try/Catch/Finally -------------------------------------------------------

  defp compile_try(meta, children, state) do
    line = Keyword.get(meta, :line, state.line)

    # children: [try_body | catch_arms] possibly with finally at end
    case children do
      [try_body | rest] ->
        {try_form, state} = do_compile_expr(try_body, state)

        {catch_clauses, after_forms, state} =
          compile_catch_and_finally(rest, line, state)

        form =
          {:try, line, [try_form], [], catch_clauses, after_forms}

        {form, state}

      _ ->
        {{:atom, line, :ok}, state}
    end
  end

  defp compile_catch_and_finally(rest, line, state) do
    # Separate match_arm nodes (catch) from non-match final expression (finally)
    {arms, finally_parts} =
      Enum.split_with(rest, fn
        {:match_arm, _, _} -> true
        _ -> false
      end)

    {catch_clauses, state} =
      Enum.map_reduce(arms, state, fn {:match_arm, arm_meta, [body]}, st ->
        pattern = Keyword.get(arm_meta, :pattern)
        {pat_form, st} = compile_pattern(pattern, st)
        {body_form, st} = do_compile_expr(body, st)

        # Erlang catch clause: {Class, Pattern, Stacktrace} -> Body
        clause =
          {:clause, line, [{:tuple, line, [{:var, line, :_}, pat_form, {:var, line, :_}]}], [], [body_form]}

        {clause, st}
      end)

    {after_forms, state} =
      case finally_parts do
        [finally_body] ->
          {form, state} = do_compile_expr(finally_body, state)
          {[form], state}

        _ ->
          {[], state}
      end

    {catch_clauses, after_forms, state}
  end

  # -- Pattern Compilation (for match arms and let destructuring) ---------------

  defp compile_pattern(ast, state) do
    case ast do
      {:literal, meta, value} ->
        compile_literal(meta, value, state)

      {:variable, _meta, "_"} ->
        {{:var, state.line, :_}, state}

      {:variable, _meta, name} ->
        var_atom = mangle_var(name)
        state = %{state | vars: Map.put(state.vars, name, var_atom)}
        {{:var, state.line, var_atom}, state}

      {:list, meta, elems} ->
        compile_list(meta, elems, state)

      {:tuple, meta, elems} ->
        compile_tuple(meta, elems, state)

      {:map, meta, pairs} ->
        compile_map(meta, pairs, state)

      # Note: cons lists are already handled by the {:list, meta, elems} clause above
      # since compile_list checks meta[:cons] internally

      {:function_call, meta, args} ->
        # Constructor pattern: Ok(x) -> {:ok, x}
        name = Keyword.get(meta, :name, "unknown")

        if constructor?(name) do
          tag = constructor_tag(name)

          {arg_forms, state} =
            Enum.map_reduce(args, state, fn arg, st ->
              compile_pattern(arg, st)
            end)

          {{:tuple, state.line, [{:atom, state.line, tag} | arg_forms]}, state}
        else
          # Regular call in pattern position -- compile as expression
          do_compile_expr({:function_call, meta, args}, state)
        end

      _ ->
        # Fallback: compile as expression
        do_compile_expr(ast, state)
    end
  end

  # -- Guard Compilation -------------------------------------------------------

  defp compile_guard(nil, _state), do: []

  defp compile_guard(guard_ast, state) do
    {form, _state} = do_compile_expr(guard_ast, state)
    [[form]]
  end

  # -- Helper: build param forms -----------------------------------------------

  defp build_param_forms(params, line, state) do
    Enum.map_reduce(params, state, fn
      {:param, _meta, name}, st ->
        var_atom = mangle_var(name)
        st = %{st | vars: Map.put(st.vars, name, var_atom)}
        {{:var, line, var_atom}, st}
    end)
  end

  # -- Name Mangling -----------------------------------------------------------

  @doc false
  def mangle_var("_"), do: :_

  # Preserve the user-intended `_name` shape so erl_lint does not warn
  # about the mangled form. `_foo` becomes `_V_foo`, not `V__foo`.
  def mangle_var("_" <> rest), do: String.to_atom("_V_" <> rest)
  def mangle_var(name), do: String.to_atom("V_" <> name)

  @doc false
  def mangle_fn_name(name) do
    name
    |> String.downcase()
    |> String.to_atom()
  end

  @doc false
  # Special case: "Erlang" in Cure source is a direct reference to the
  # BEAM Erlang stdlib module :erlang, not a user-defined Cure module.
  def cure_module_to_atom("Erlang"), do: :erlang

  def cure_module_to_atom(name) do
    # "Std.Core" -> :"Cure.Std.Core"
    # Elixir-style module atom with Cure. prefix, preserving PascalCase
    String.to_atom("Cure." <> name)
  end

  # -- Operator Mapping --------------------------------------------------------

  defp cure_op_to_erlang(:+), do: :+
  defp cure_op_to_erlang(:-), do: :-
  defp cure_op_to_erlang(:*), do: :*
  defp cure_op_to_erlang(:/), do: :div
  defp cure_op_to_erlang(:%), do: :rem
  defp cure_op_to_erlang(:==), do: :==
  defp cure_op_to_erlang(:!=), do: :"/="
  defp cure_op_to_erlang(:<), do: :<
  defp cure_op_to_erlang(:>), do: :>
  defp cure_op_to_erlang(:<=), do: :"=<"
  defp cure_op_to_erlang(:>=), do: :>=
  defp cure_op_to_erlang(:and), do: :andalso
  defp cure_op_to_erlang(:or), do: :orelse
  defp cure_op_to_erlang(:not), do: :not
  defp cure_op_to_erlang(op), do: op

  # -- Constructor Helpers -----------------------------------------------------

  defp constructor?(name) when is_binary(name) do
    case String.first(name) do
      nil -> false
      first -> first == String.upcase(first) and first != String.downcase(first)
    end
  end

  defp constructor?(_), do: false

  defp constructor_tag(name) do
    name
    |> Macro.underscore()
    |> String.to_atom()
  end

  # -- Import Resolution --------------------------------------------------------

  defp resolve_import(_fn_atom, _arity, []), do: :not_found

  defp resolve_import(fn_atom, arity, [mod | rest]) do
    if module_exports?(mod, fn_atom, arity) do
      {:ok, mod}
    else
      resolve_import(fn_atom, arity, rest)
    end
  end

  defp module_exports?(mod, fn_atom, arity) do
    case :code.ensure_loaded(mod) do
      {:module, ^mod} ->
        exports = mod.module_info(:exports)
        {fn_atom, arity} in exports

      _ ->
        false
    end
  end

  # -- Protocol Call Resolution -------------------------------------------------

  defp resolve_protocol_call(name, arity, line) do
    fn_atom = mangle_fn_name(name)
    # Check all known protocol impls for a method matching this name
    # This enables cross-module dispatch: if show/1 is registered
    # in the protocol registry, emit a remote call to the providing module
    impls = ProtocolRegistry.list_impls_by_method(name)

    case impls do
      [{_type, _method, module} | _] ->
        {:ok,
         {:call, line, {:remote, line, {:atom, line, module}, {:atom, line, fn_atom}}, build_arg_vars(arity, line)}}

      [] ->
        :not_found
    end
  end

  defp build_arg_vars(0, _line), do: []

  defp build_arg_vars(n, line) do
    Enum.map(0..(n - 1), fn i -> {:var, line, String.to_atom("V_arg#{i}")} end)
  end

  # -- Misc Helpers ------------------------------------------------------------

  defp find_container(children) do
    Enum.find(children, fn
      {:container, meta, _body} when is_list(meta) -> true
      _ -> false
    end)
  end

  # When the parser produces {:block, _, [container, block_with_defs]},
  # merge the definitions from sibling nodes into the container body.
  defp merge_sibling_defs(body, children) do
    sibling_defs =
      Enum.flat_map(children, fn
        {:container, _, _} -> []
        {:block, _, items} -> items
        other -> [other]
      end)

    body ++ sibling_defs
  end

  defp build_list([], line), do: {nil, line}
  defp build_list([h | t], line), do: {:cons, line, h, build_list(t, line)}
end
