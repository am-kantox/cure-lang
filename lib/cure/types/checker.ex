defmodule Cure.Types.Checker do
  @moduledoc """
  Bidirectional type checker for the Cure programming language.

  Operates on MetaAST 3-tuples produced by `Cure.Compiler.Parser`.
  Validates types, rejects ill-typed programs, and emits
  `:type_checker` pipeline events.

  ## Two-pass module checking

  1. **Signature collection** -- scans `function_def` nodes and `:struct`
     containers. For each `rec` definition, the field schema is registered
     in `Cure.Types.Env.types` as `{:record, name_atom, field_map}`.
  2. **Body checking** -- checks each function body against its declared
     return type, using the field schemas registered in pass 1.

  ## Record type inference

  - `rec Point` makes the type checker aware that `p : Point` gives
    `p.x : Int`, `p.y : Int`, etc.
  - Record construction `Point{x: 1, y: 2}` infers type `{:named, "Point"}`.
  - Field access `p.field` on a `{:named, "T"}` value looks up the field
    type in `Env.types["T"]`; access on `:any` produces `:any`.
  - Record update `Point{p | x: new_x}` type-checks each override field
    against the schema and returns `{:named, "Point"}`.

  ## Usage

      {:ok, ast} = Cure.Compiler.Parser.parse(tokens)
      case Cure.Types.Checker.check_module(ast) do
        {:ok, _typed_ast} -> # proceed to codegen
        {:error, errors}  -> # report errors
      end

  ## Pipeline Events

  - `{:type_checker, :type_inferred, {ast, type}, meta}`
  - `{:type_checker, :type_checked, {name, type}, meta}`
  - `{:type_checker, :type_error, error, meta}`
  """

  alias Cure.Types.{Type, Env, PatternChecker, GuardRefinement, Effects}
  alias Cure.Pipeline.Events

  @type error :: {atom(), String.t(), keyword()}

  # -- Public API --------------------------------------------------------------

  @doc """
  Type-check a module AST node.

  Returns `{:ok, ast}` if well-typed, `{:error, errors}` otherwise.
  """
  @spec check_module(tuple(), keyword()) :: {:ok, tuple()} | {:error, [error()]}
  def check_module(ast, opts \\ []) do
    emit? = Keyword.get(opts, :emit_events, true)
    file = Keyword.get(opts, :file, "nofile")
    env = Env.new()

    case ast do
      {:container, meta, body} when is_list(meta) ->
        case Keyword.get(meta, :container_type) do
          :module ->
            check_module_body(body, env, emit?, file)

          _ ->
            {:ok, ast}
        end

      {:block, _, children} when is_list(children) ->
        case Enum.find(children, fn
               {:container, m, _} when is_list(m) -> true
               _ -> false
             end) do
          {:container, meta, body} ->
            case Keyword.get(meta, :container_type) do
              :module -> check_module_body(body, env, emit?, file)
              _ -> {:ok, ast}
            end

          nil ->
            {:ok, ast}
        end

      _ ->
        {:ok, ast}
    end
  end

  @doc """
  Infer the type of a single expression AST node in an empty environment.

  Useful for testing.
  """
  @spec infer_expr(tuple()) :: {:ok, term()} | {:error, error()}
  def infer_expr(ast) do
    env = Env.new()

    case infer(env, ast, false, "nofile") do
      {:ok, type, _env} -> {:ok, type}
      {:error, _} = err -> err
    end
  end

  # -- Module Body (two-pass) --------------------------------------------------

  defp check_module_body(stmts, env, emit?, file) do
    # Pass 1: collect function signatures (including protocol methods)
    env = collect_signatures(stmts, env)

    # Pass 2: check function bodies (regular fns + impl method bodies)
    errors =
      Enum.flat_map(stmts, fn
        {:function_def, meta, body} ->
          check_function_def(meta, body, env, emit?, file)

        {:container, meta, body} when is_list(meta) ->
          case Keyword.get(meta, :container_type) do
            :trait ->
              # Check impl method bodies
              Enum.flat_map(body, fn
                {:function_def, m, b} -> check_function_def(m, b, env, emit?, file)
                _ -> []
              end)

            _ ->
              []
          end

        _ ->
          []
      end)

    if errors == [] do
      {:ok, :module_ok}
    else
      {:error, errors}
    end
  end

  defp collect_signatures(stmts, env) do
    Enum.reduce(stmts, env, fn
      {:function_def, meta, _body}, env ->
        register_fn_signature(meta, env)

      # Register protocol method signatures so calling them type-checks,
      # and record field schemas for type-safe field access.
      {:container, meta, body}, env when is_list(meta) ->
        case Keyword.get(meta, :container_type) do
          :struct ->
            name = Keyword.get(meta, :name)

            field_map =
              Enum.reduce(body, %{}, fn
                {:param, pmeta, field_name}, acc ->
                  type_ast = Keyword.get(pmeta, :type)
                  Map.put(acc, field_name, Type.resolve(type_ast))

                _, acc ->
                  acc
              end)

            Env.extend_type(env, name, {:record, String.to_atom(String.downcase(name)), field_map})

          :protocol ->
            Enum.reduce(body, env, fn
              {:function_def, m, _}, e -> register_fn_signature(m, e)
              _, e -> e
            end)

          _ ->
            env
        end

      _, env ->
        env
    end)
  end

  defp register_fn_signature(meta, env) do
    name = Keyword.get(meta, :name, "unknown")
    params = Keyword.get(meta, :params, [])
    return_type_ast = Keyword.get(meta, :return_type)
    extern = Keyword.get(meta, :extern)
    guard_ast = Keyword.get(meta, :guards)

    param_types =
      Enum.map(params, fn {:param, pmeta, _name} ->
        type_ast = Keyword.get(pmeta, :type)
        Type.resolve(type_ast)
      end)

    param_names =
      Enum.map(params, fn {:param, _pmeta, pname} -> pname end)

    ret_type =
      cond do
        extern != nil and return_type_ast != nil -> Type.resolve(return_type_ast)
        return_type_ast != nil -> Type.resolve(return_type_ast)
        true -> :any
      end

    fn_type =
      if guard_ast do
        {:constrained_fun, param_types, ret_type, guard_ast, param_names}
      else
        {:fun, param_types, ret_type}
      end

    Env.extend(env, name, fn_type)
  end

  # -- Function Definition Check -----------------------------------------------

  defp check_function_def(meta, body, env, emit?, file) do
    name = Keyword.get(meta, :name, "unknown")
    params = Keyword.get(meta, :params, [])
    return_type_ast = Keyword.get(meta, :return_type)
    extern = Keyword.get(meta, :extern)
    clauses = Keyword.get(meta, :clauses)
    line = Keyword.get(meta, :line, 1)
    declared_effects = Keyword.get(meta, :effects)

    declared_ret = if return_type_ast, do: Type.resolve(return_type_ast), else: nil

    cond do
      # @extern: trust declared types, classify effects
      extern != nil ->
        extern_effects = Effects.classify_extern(extern)

        if emit? do
          ret = declared_ret || :any
          Events.emit(:type_checker, :type_checked, {name, {:fun, [], ret}}, Events.meta(file, line))
          Effects.emit_effects(name, extern_effects, file, line)
        end

        []

      # Multi-clause function
      clauses != nil ->
        type_errors = check_multi_clause(name, clauses, declared_ret, env, emit?, file, line)

        # Infer effects from all clause bodies
        if emit? do
          clause_effects =
            Enum.reduce(clauses, MapSet.new(), fn %{body: clause_body}, acc ->
              Enum.reduce(clause_body, acc, fn b, a ->
                MapSet.union(a, Effects.infer_effects(b, env))
              end)
            end)

          Effects.emit_effects(name, clause_effects, file, line)
          maybe_check_declared_effects(declared_effects, clause_effects, name, file, line)
        end

        type_errors

      # Regular function with body
      true ->
        type_errors = check_single_fn(name, params, body, declared_ret, env, emit?, file, line)

        # Infer effects from function body
        if emit? do
          body_effects =
            Enum.reduce(body, MapSet.new(), fn b, acc ->
              MapSet.union(acc, Effects.infer_effects(b, env))
            end)

          Effects.emit_effects(name, body_effects, file, line)
          maybe_check_declared_effects(declared_effects, body_effects, name, file, line)
        end

        type_errors
    end
  end

  defp maybe_check_declared_effects(nil, _inferred, _name, _file, _line), do: :ok

  defp maybe_check_declared_effects(declared, inferred, name, file, line) do
    case Effects.check_effects(declared, inferred, name) do
      :ok ->
        :ok

      {:warning, msg} ->
        Events.emit(:type_checker, :type_warning, {:effect_over_annotation, msg, line: line}, Events.meta(file, line))

      {:error, msg} ->
        Events.emit(:type_checker, :effect_error, {:effect_violation, msg, line: line}, Events.meta(file, line))
    end
  end

  defp check_single_fn(name, params, body, declared_ret, env, emit?, file, line) do
    fn_env = Env.push_scope(env)

    # Collect param name -> base type pairs
    param_info =
      Enum.map(params, fn {:param, pmeta, pname} ->
        type_ast = Keyword.get(pmeta, :type)
        {pname, Type.resolve(type_ast)}
      end)

    fn_env =
      Enum.reduce(param_info, fn_env, fn {pname, ptype}, e ->
        Env.extend(e, pname, ptype)
      end)

    # Apply guard refinement: if a guard is present, refine param types
    guard_ast = Keyword.get(Keyword.new(), :guards)
    fn_env = GuardRefinement.refine_env(fn_env, guard_ast, param_info)

    case body do
      [body_ast] ->
        case infer(fn_env, body_ast, emit?, file) do
          {:ok, body_type, _env} ->
            check_return_type(name, body_type, declared_ret, emit?, file, line)

          {:error, err} ->
            [err]
        end

      [] ->
        check_return_type(name, :unit, declared_ret, emit?, file, line)

      multiple ->
        check_body_sequence(name, multiple, declared_ret, fn_env, emit?, file, line)
    end
  end

  defp check_body_sequence(name, exprs, declared_ret, env, emit?, file, line) do
    result =
      Enum.reduce_while(exprs, {:ok, :unit, env}, fn expr, {:ok, _prev_type, e} ->
        case infer(e, expr, emit?, file) do
          {:ok, t, e2} -> {:cont, {:ok, t, e2}}
          {:error, _} = err -> {:halt, err}
        end
      end)

    case result do
      {:ok, body_type, _} -> check_return_type(name, body_type, declared_ret, emit?, file, line)
      {:error, err} -> [err]
    end
  end

  defp check_multi_clause(name, clauses, declared_ret, env, emit?, file, line) do
    # Extract guards for coverage analysis
    guard_asts = Enum.map(clauses, fn %{guard: guard} -> guard end)

    # Guard coverage analysis: check if guards cover all cases
    # Use the first variable-typed param for SMT analysis
    first_var_clause =
      Enum.find(clauses, fn %{params: params} ->
        Enum.any?(params, fn
          {:variable, _, _} -> true
          _ -> false
        end)
      end)

    if first_var_clause && Enum.any?(guard_asts, &(&1 != nil)) do
      first_var =
        Enum.find(first_var_clause.params, fn
          {:variable, _, _} -> true
          _ -> false
        end)

      case first_var do
        {:variable, _, vname} ->
          case GuardRefinement.check_guard_coverage(guard_asts, vname, :int) do
            {:non_exhaustive, desc} ->
              if emit? do
                Events.emit(
                  :type_checker,
                  :type_warning,
                  {:non_exhaustive_guards, "function '#{name}': #{desc}", line: line},
                  Events.meta(file, line)
                )
              end

            _ ->
              :ok
          end

        _ ->
          :ok
      end
    end

    # Type-check each clause with guard-refined environment
    clause_types =
      Enum.map(clauses, fn %{params: params, guard: guard, body: body_list} ->
        clause_env = Env.push_scope(env)

        # Bind pattern variables
        param_info =
          Enum.flat_map(params, fn
            {:variable, _, vname} -> [{vname, :any}]
            _ -> []
          end)

        clause_env =
          Enum.reduce(param_info, clause_env, fn {vname, vtype}, e ->
            Env.extend(e, vname, vtype)
          end)

        # Apply guard refinement
        clause_env = GuardRefinement.refine_env(clause_env, guard, param_info)

        case body_list do
          [body_ast] ->
            case infer(clause_env, body_ast, emit?, file) do
              {:ok, t, _} -> {:ok, t}
              err -> err
            end

          _ ->
            {:ok, :any}
        end
      end)

    errors = for {:error, e} <- clause_types, do: e

    if errors != [] do
      errors
    else
      types = for {:ok, t} <- clause_types, do: t
      joined = Enum.reduce(types, :never, &Type.join/2)
      check_return_type(name, joined, declared_ret, emit?, file, line)
    end
  end

  defp check_return_type(name, body_type, nil, emit?, file, line) do
    if emit? do
      Events.emit(:type_checker, :type_checked, {name, body_type}, Events.meta(file, line))
    end

    []
  end

  defp check_return_type(name, body_type, {:type_hole, :infer}, emit?, file, line) do
    # Type hole: report the inferred type as a hint
    if emit? do
      Events.emit(
        :type_checker,
        :type_hole_inferred,
        {name, :return_type, body_type},
        Events.meta(file, line)
      )
    end

    []
  end

  defp check_return_type(name, body_type, declared_ret, emit?, file, line) do
    if Type.subtype?(body_type, declared_ret) do
      if emit? do
        Events.emit(:type_checker, :type_checked, {name, declared_ret}, Events.meta(file, line))
      end

      []
    else
      err =
        {:type_mismatch,
         "function '#{name}' declared return type #{Type.display(declared_ret)} " <>
           "but body has type #{Type.display(body_type)}", line: line}

      if emit? do
        Events.emit(:type_checker, :type_error, err, Events.meta(file, line))
      end

      [err]
    end
  end

  # -- Expression Type Inference -----------------------------------------------

  defp infer(env, ast, emit?, file) do
    # Attach emit/file to env so deep fallback clauses can access them
    env = Map.put(env, :emit_events, emit?) |> Map.put(:file, file)
    result = do_infer(env, ast)

    case result do
      {:ok, type, new_env} ->
        if emit? do
          line = extract_line(ast)
          Events.emit(:type_checker, :type_inferred, {ast, type}, Events.meta(file, line))
        end

        {:ok, type, new_env}

      {:error, err} ->
        if emit? do
          Events.emit(:type_checker, :type_error, err, Events.meta(file, 1))
        end

        {:error, err}
    end
  end

  # -- Range -------------------------------------------------------------------

  defp do_infer(env, {:range, _meta, [from, to]}) do
    with {:ok, _, env} <- do_infer(env, from),
         {:ok, _, env} <- do_infer(env, to) do
      {:ok, {:list, :int}, env}
    end
  end

  # -- Literals ----------------------------------------------------------------

  defp do_infer(env, {:literal, meta, _value}) do
    type =
      case Keyword.get(meta, :subtype) do
        :integer -> :int
        :float -> :float
        :string -> :string
        :boolean -> :bool
        :null -> :unit
        :symbol -> :atom
        :char -> :char
        :regex -> :regex
        _ -> :any
      end

    {:ok, type, env}
  end

  # -- Variables ---------------------------------------------------------------

  defp do_infer(env, {:variable, _meta, "_"}) do
    {:ok, :any, env}
  end

  defp do_infer(env, {:variable, meta, name}) do
    case Env.lookup(env, name) do
      {:ok, type} ->
        {:ok, type, env}

      :error ->
        line = Keyword.get(meta, :line, 1)

        {:error, {:unbound_variable, "undefined variable '#{name}'", line: line}}
    end
  end

  # -- Binary Operators --------------------------------------------------------

  defp do_infer(env, {:binary_op, meta, [left, right]}) do
    op = Keyword.get(meta, :operator)
    category = Keyword.get(meta, :category)
    line = Keyword.get(meta, :line, 1)

    with {:ok, lt, env} <- do_infer(env, left),
         {:ok, rt, env} <- do_infer(env, right) do
      case category do
        :arithmetic ->
          cond do
            Type.numeric?(lt) and Type.numeric?(rt) ->
              {:ok, Type.join(lt, rt), env}

            lt == :any or rt == :any ->
              {:ok, :any, env}

            true ->
              {:error,
               {:type_mismatch,
                "operator '#{op}' expects numeric operands, got #{Type.display(lt)} and #{Type.display(rt)}",
                line: line}}
          end

        :comparison ->
          cond do
            Type.compatible?(lt, rt) or lt == :any or rt == :any ->
              {:ok, :bool, env}

            true ->
              {:error, {:type_mismatch, "cannot compare #{Type.display(lt)} with #{Type.display(rt)}", line: line}}
          end

        :boolean ->
          cond do
            (lt == :bool or lt == :any) and (rt == :bool or rt == :any) ->
              {:ok, :bool, env}

            true ->
              {:error,
               {:type_mismatch,
                "operator '#{op}' expects Bool operands, got #{Type.display(lt)} and #{Type.display(rt)}", line: line}}
          end

        :string ->
          cond do
            (lt == :string or lt == :any) and (rt == :string or rt == :any) ->
              {:ok, :string, env}

            true ->
              {:error,
               {:type_mismatch, "'<>' expects String operands, got #{Type.display(lt)} and #{Type.display(rt)}",
                line: line}}
          end

        _ ->
          {:ok, :any, env}
      end
    end
  end

  # -- Unary Operators ---------------------------------------------------------

  defp do_infer(env, {:unary_op, meta, [operand]}) do
    category = Keyword.get(meta, :category)
    line = Keyword.get(meta, :line, 1)

    with {:ok, ot, env} <- do_infer(env, operand) do
      case category do
        :arithmetic ->
          if Type.numeric?(ot) or ot == :any do
            {:ok, ot, env}
          else
            {:error, {:type_mismatch, "unary '-' expects numeric operand, got #{Type.display(ot)}", line: line}}
          end

        :boolean ->
          if ot == :bool or ot == :any do
            {:ok, :bool, env}
          else
            {:error, {:type_mismatch, "'not' expects Bool operand, got #{Type.display(ot)}", line: line}}
          end

        _ ->
          {:ok, :any, env}
      end
    end
  end

  # -- Function Calls ----------------------------------------------------------

  defp do_infer(env, {:function_call, meta, args}) do
    name = Keyword.get(meta, :name, "unknown")
    line = Keyword.get(meta, :line, 1)

    if Keyword.get(meta, :record, false) do
      # Record construction: TypeName{field: val, ...} -- infer field arg types
      # (for side-effects / error propagation) then return the named type.
      {_field_types, env} = infer_args(env, args)
      {:ok, {:named, name}, env}
    else
      {arg_types, env} = infer_args(env, args)

      case Env.lookup(env, name) do
        {:ok, {:fun, param_types, ret_type}} ->
          check_fn_call(name, param_types, ret_type, arg_types, line, env)

        {:ok, {:constrained_fun, param_types, ret_type, guard_ast, param_names}} ->
          case check_fn_call(name, param_types, ret_type, arg_types, line, env) do
            {:ok, _, _} = ok ->
              # Verify guard constraint via SMT
              verify_call_constraint(name, guard_ast, param_names, args, line, env)
              ok

            err ->
              err
          end

        {:ok, _other} ->
          {:ok, :any, env}

        :error ->
          {:ok, :any, env}
      end
    end
  end

  # -- Let Binding

  defp do_infer(env, {:assignment, meta, [pattern, value]}) do
    annotation_ast = Keyword.get(meta, :type_annotation)
    line = Keyword.get(meta, :line, 1)

    with {:ok, val_type, env} <- do_infer(env, value) do
      if annotation_ast do
        declared = Type.resolve(annotation_ast)

        if Type.subtype?(val_type, declared) do
          env = bind_pattern(env, pattern, declared)
          {:ok, declared, env}
        else
          {:error,
           {:type_mismatch, "let annotation expects #{Type.display(declared)}, got #{Type.display(val_type)}",
            line: line}}
        end
      else
        env = bind_pattern(env, pattern, val_type)
        {:ok, val_type, env}
      end
    end
  end

  # -- Augmented Assignment ----------------------------------------------------

  defp do_infer(env, {:augmented_assignment, _meta, [var, value]}) do
    with {:ok, _, env} <- do_infer(env, var),
         {:ok, vt, env} <- do_infer(env, value) do
      {:ok, vt, env}
    end
  end

  # -- Conditional (if/else) ---------------------------------------------------

  defp do_infer(env, {:conditional, meta, [cond_ast, then_ast, else_ast]}) do
    line = Keyword.get(meta, :line, 1)

    with {:ok, ct, env} <- do_infer(env, cond_ast) do
      if ct != :bool and ct != :any do
        {:error, {:type_mismatch, "if condition must be Bool, got #{Type.display(ct)}", line: line}}
      else
        # Path-sensitive: refine env in each branch based on the condition
        # Extract variable constraints from the condition for refinement
        then_env = refine_env_from_condition(env, cond_ast, true)
        else_env = refine_env_from_condition(env, cond_ast, false)

        with {:ok, tt, _} <- do_infer(then_env, then_ast),
             {:ok, et, _} <- do_infer(else_env, else_ast) do
          if Type.compatible?(tt, et) or tt == :any or et == :any do
            {:ok, Type.join(tt, et), env}
          else
            {:error,
             {:type_mismatch, "if branches have incompatible types: #{Type.display(tt)} vs #{Type.display(et)}",
              line: line}}
          end
        end
      end
    end
  end

  # -- Pattern Match -----------------------------------------------------------

  defp do_infer(env, {:pattern_match, meta, [scrutinee | arms]}) do
    with {:ok, scrut_type, env} <- do_infer(env, scrutinee) do
      # Extract pattern ASTs for exhaustiveness checking
      patterns = Enum.map(arms, fn {:match_arm, arm_meta, _} -> Keyword.get(arm_meta, :pattern) end)

      # Run exhaustiveness check
      case PatternChecker.check_match(scrut_type, patterns) do
        {:non_exhaustive, missing} ->
          line = Keyword.get(meta, :line, 1)

          warning =
            {:non_exhaustive_match, "match expression is not exhaustive, missing: #{Enum.join(missing, ", ")}",
             line: line}

          # Emit as warning (not error) -- match still compiles
          Events.emit(:type_checker, :type_warning, warning, Events.meta("nofile", line))

        _ ->
          :ok
      end

      # Type-check arm bodies with pattern variables bound
      arm_types =
        Enum.map(arms, fn {:match_arm, arm_meta, [body]} ->
          arm_env = Env.push_scope(env)
          pattern = Keyword.get(arm_meta, :pattern)
          arm_env = bind_pattern_vars(arm_env, pattern, scrut_type)

          case do_infer(arm_env, body) do
            {:ok, t, _} -> {:ok, t}
            err -> err
          end
        end)

      errors = for {:error, e} <- arm_types, do: e

      if errors != [] do
        {:error, hd(errors)}
      else
        types = for {:ok, t} <- arm_types, do: t
        joined = Enum.reduce(types, :never, &Type.join/2)
        {:ok, joined, env}
      end
    end
  end

  # -- Block -------------------------------------------------------------------

  defp do_infer(env, {:block, _meta, exprs}) do
    block_env = Env.push_scope(env)

    result =
      Enum.reduce_while(exprs, {:ok, :unit, block_env}, fn expr, {:ok, _prev, e} ->
        case do_infer(e, expr) do
          {:ok, t, e2} -> {:cont, {:ok, t, e2}}
          {:error, _} = err -> {:halt, err}
        end
      end)

    case result do
      {:ok, t, _} -> {:ok, t, env}
      {:error, _} = err -> err
    end
  end

  # -- List --------------------------------------------------------------------

  defp do_infer(env, {:list, meta, elems}) do
    is_cons = Keyword.get(meta, :cons, false)

    case elems do
      [] ->
        {:ok, {:list, :any}, env}

      _ when is_cons ->
        [head, tail] = elems

        with {:ok, ht, env} <- do_infer(env, head),
             {:ok, _tt, env} <- do_infer(env, tail) do
          {:ok, {:list, ht}, env}
        end

      _ ->
        {elem_types, env} = infer_args(env, elems)
        elem_type = Enum.reduce(elem_types, :never, &Type.join/2)
        {:ok, {:list, elem_type}, env}
    end
  end

  # -- Tuple -------------------------------------------------------------------

  defp do_infer(env, {:tuple, _meta, elems}) do
    {elem_types, env} = infer_args(env, elems)
    {:ok, {:tuple, elem_types}, env}
  end

  # -- Map ---------------------------------------------------------------------

  defp do_infer(env, {:map, _meta, pairs}) do
    case pairs do
      [] ->
        {:ok, {:map, :any, :any}, env}

      _ ->
        {kv_types, env} =
          Enum.map_reduce(pairs, env, fn {:pair, _, [key, val]}, e ->
            {:ok, kt, e} = do_infer(e, key)
            {:ok, vt, e} = do_infer(e, val)
            {{kt, vt}, e}
          end)

        {k_types, v_types} = Enum.unzip(kv_types)
        kt = Enum.reduce(k_types, :never, &Type.join/2)
        vt = Enum.reduce(v_types, :never, &Type.join/2)
        {:ok, {:map, kt, vt}, env}
    end
  end

  # -- Lambda ------------------------------------------------------------------

  defp do_infer(env, {:lambda, meta, [body]}) do
    params = Keyword.get(meta, :params, [])

    lambda_env = Env.push_scope(env)

    {param_types, lambda_env} =
      Enum.map_reduce(params, lambda_env, fn {:param, _, pname}, e ->
        e = Env.extend(e, pname, :any)
        {:any, e}
      end)

    case do_infer(lambda_env, body) do
      {:ok, ret_type, _} -> {:ok, {:fun, param_types, ret_type}, env}
      {:error, _} = err -> err
    end
  end

  # -- String Interpolation ----------------------------------------------------

  defp do_infer(env, {:string_interpolation, _meta, _parts}) do
    {:ok, :string, env}
  end

  # -- Early Return / Throw / Yield --------------------------------------------

  defp do_infer(env, {:early_return, _meta, [expr]}) do
    with {:ok, t, env} <- do_infer(env, expr), do: {:ok, t, env}
  end

  defp do_infer(env, {:throw, _meta, [expr]}) do
    with {:ok, _, env} <- do_infer(env, expr), do: {:ok, :never, env}
  end

  defp do_infer(env, {:yield, _meta, [expr]}) do
    with {:ok, t, env} <- do_infer(env, expr), do: {:ok, t, env}
  end

  # -- Comprehension -----------------------------------------------------------

  defp do_infer(env, {:comprehension, _meta, [body | _qualifiers]}) do
    case do_infer(env, body) do
      {:ok, bt, env} -> {:ok, {:list, bt}, env}
      err -> err
    end
  end

  # -- Containers (nested modules, etc.) -- skip in expression position --------

  defp do_infer(env, {:container, _meta, _body}), do: {:ok, :any, env}
  defp do_infer(env, {:function_def, _meta, _body}), do: {:ok, :any, env}
  defp do_infer(env, {:import, _meta, _}), do: {:ok, :any, env}
  defp do_infer(env, {:exception_handling, _meta, _}), do: {:ok, :any, env}
  defp do_infer(env, {:async_operation, _meta, _}), do: {:ok, :any, env}
  defp do_infer(env, {:decorator, _meta, _}), do: {:ok, :any, env}
  defp do_infer(env, {:property, _meta, _}), do: {:ok, :any, env}

  # -- Record Update -----------------------------------------------------------

  defp do_infer(env, {:record_update, meta, [base | fields]}) do
    line = Keyword.get(meta, :line, 1)

    with {:ok, base_type, env} <- do_infer(env, base) do
      # Type-check each override value against the declared field type.
      errors =
        Enum.flat_map(fields, fn
          {:pair, _, [key, value]} ->
            field_name =
              case key do
                {:literal, [subtype: :symbol], atom} -> Atom.to_string(atom)
                _ -> nil
              end

            case do_infer(env, value) do
              {:ok, val_type, _} when field_name != nil ->
                expected = resolve_record_field(env, base_type, field_name)

                if expected == :any or Type.subtype?(val_type, expected) do
                  []
                else
                  [
                    {:type_mismatch,
                     "field '#{field_name}' expects #{Type.display(expected)} " <>
                       "but update value has type #{Type.display(val_type)}", line: line}
                  ]
                end

              {:error, err} ->
                [err]

              _ ->
                []
            end

          _ ->
            []
        end)

      case errors do
        [] -> {:ok, base_type, env}
        [first | _] -> {:error, first}
      end
    end
  end

  # -- Attribute Access --------------------------------------------------------

  defp do_infer(env, {:attribute_access, meta, [obj]}) do
    field_name = Keyword.get(meta, :attribute)

    with {:ok, obj_type, env} <- do_infer(env, obj) do
      {:ok, resolve_record_field(env, obj_type, field_name), env}
    end
  end

  # -- Fallback ----------------------------------------------------------------

  defp do_infer(env, ast) do
    tag =
      if is_tuple(ast) and tuple_size(ast) >= 1,
        do: elem(ast, 0),
        else: :unknown

    line =
      if is_tuple(ast) and tuple_size(ast) >= 2 do
        case elem(ast, 1) do
          meta when is_list(meta) -> Keyword.get(meta, :line, 0)
          _ -> 0
        end
      else
        0
      end

    if Map.get(env, :emit_events, false) do
      file = Map.get(env, :file, "nofile")

      Events.emit(
        :type_checker,
        :type_warning,
        {:unrecognized_node, "unrecognized AST node '#{tag}' inferred as Any", line: line},
        Events.meta(file, line)
      )
    end

    {:ok, :any, env}
  end

  defp resolve_record_field(env, {:named, rec_name}, field_name) do
    case Env.lookup_type(env, rec_name) do
      {:ok, {:record, _, field_map}} -> Map.get(field_map, field_name, :any)
      _ -> :any
    end
  end

  defp resolve_record_field(_env, _type, _field_name), do: :any

  # -- Path-Sensitive Refinement ------------------------------------------------

  defp refine_env_from_condition(env, cond_ast, branch) do
    # Extract variable names from the condition
    vars = GuardRefinement.extract_constraints(cond_ast)

    if map_size(vars) > 0 do
      predicate =
        if branch do
          cond_ast
        else
          {:unary_op, [operator: :not, category: :boolean], [cond_ast]}
        end

      # For each variable in the condition, refine its type
      Enum.reduce(vars, env, fn {var_name, _}, e ->
        case Env.lookup(e, var_name) do
          {:ok, base_type} when is_atom(base_type) ->
            refined = Cure.Types.Refinement.new(base_type, var_name, predicate)
            Env.extend(e, var_name, refined)

          _ ->
            e
        end
      end)
    else
      env
    end
  end

  # -- Constrained Call Helpers ------------------------------------------------

  defp check_fn_call(name, param_types, ret_type, arg_types, line, env) do
    cond do
      length(param_types) != length(arg_types) ->
        {:error,
         {:arity_mismatch, "function '#{name}' expects #{length(param_types)} arguments, got #{length(arg_types)}",
          line: line}}

      params_match?(param_types, arg_types) ->
        {:ok, ret_type, env}

      true ->
        {:error, {:type_mismatch, "argument type mismatch in call to '#{name}'", line: line}}
    end
  end

  defp verify_call_constraint(name, guard_ast, param_names, args, line, _env) do
    bindings =
      Enum.zip(param_names, args)
      |> Enum.flat_map(fn
        {pname, {:literal, meta, value}} ->
          if Keyword.get(meta, :subtype) == :integer do
            [{pname, {:literal, [subtype: :integer], value}}]
          else
            []
          end

        _ ->
          []
      end)
      |> Map.new()

    if map_size(bindings) > 0 do
      substituted = Cure.Types.Dependent.substitute_expr_public(guard_ast, bindings)

      case Cure.SMT.Solver.check_sat(substituted) do
        :unsat ->
          Events.emit(
            :type_checker,
            :type_warning,
            {:constraint_violation, "call to '#{name}': guard constraint may be violated", line: line},
            Events.meta("nofile", line)
          )

        _ ->
          :ok
      end
    end
  end

  # -- Helpers -----------------------------------------------------------------

  defp infer_args(env, args) do
    Enum.map_reduce(args, env, fn arg, e ->
      case do_infer(e, arg) do
        {:ok, t, e2} -> {t, e2}
        {:error, _} -> {:any, e}
      end
    end)
  end

  defp params_match?(param_types, arg_types) do
    Enum.zip(param_types, arg_types)
    |> Enum.all?(fn {p, a} -> Type.subtype?(a, p) or p == :any or a == :any end)
  end

  defp bind_pattern(env, {:variable, _, "_"}, _type), do: env
  defp bind_pattern(env, {:variable, _, name}, type), do: Env.extend(env, name, type)
  defp bind_pattern(env, _, _type), do: env

  # Recursively bind all variables introduced by a match arm pattern.
  defp bind_pattern_vars(env, nil, _type), do: env
  defp bind_pattern_vars(env, {:variable, _, "_"}, _type), do: env
  defp bind_pattern_vars(env, {:variable, _, name}, type), do: Env.extend(env, name, type)
  defp bind_pattern_vars(env, {:literal, _, _}, _type), do: env

  defp bind_pattern_vars(env, {:list, meta, elems}, type) do
    elem_type =
      case type do
        {:list, t} -> t
        _ -> :any
      end

    if Keyword.get(meta, :cons, false) do
      case elems do
        [head, tail] ->
          env = bind_pattern_vars(env, head, elem_type)
          bind_pattern_vars(env, tail, type)

        _ ->
          env
      end
    else
      Enum.reduce(elems, env, &bind_pattern_vars(&2, &1, elem_type))
    end
  end

  defp bind_pattern_vars(env, {:function_call, _meta, args}, _type) do
    Enum.reduce(args, env, &bind_pattern_vars(&2, &1, :any))
  end

  defp bind_pattern_vars(env, {:tuple, _, elems}, _type) do
    Enum.reduce(elems, env, &bind_pattern_vars(&2, &1, :any))
  end

  defp bind_pattern_vars(env, _, _type), do: env

  defp extract_line({_, meta, _}) when is_list(meta), do: Keyword.get(meta, :line, 1)
  defp extract_line(_), do: 1
end
