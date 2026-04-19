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

  # v0.20.0: `Cure.Types.PatternRefinement` provides the narrowing
  # pass documented in the module's `@moduledoc`. It is not aliased
  # here because `bind_pattern_vars/3` below keeps its existing
  # precise element typing for tuples/lists/records/maps; callers
  # that need the narrowed scrutinee type (disjoint-tag or literal
  # equality witnesses) can call `Cure.Types.PatternRefinement.narrow/2`
  # directly. Future releases can route `do_infer({:pattern_match, ...})`
  # through it to propagate narrowing into match-arm bodies.

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

          :proof ->
            # v0.19.0: proof containers use the same two-pass check
            # as modules, plus a shape gate that requires every
            # binding to return Eq(...) or a refinement.
            check_proof_body(body, env, emit?, file)

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
              :proof -> check_proof_body(body, env, emit?, file)
              _ -> {:ok, ast}
            end

          nil ->
            {:ok, ast}
        end

      _ ->
        {:ok, ast}
    end
  end

  # -- Proof Body (v0.19.0) ----------------------------------------------------
  #
  # Every top-level function in a proof container must return an `Eq(...)`
  # type or a refinement. Other bindings are rejected with `E026`.
  defp check_proof_body(stmts, env, emit?, file) do
    base_result = check_module_body(stmts, env, emit?, file)

    shape_errors =
      Enum.flat_map(stmts, fn
        {:function_def, meta, _body} ->
          ret_ast = Keyword.get(meta, :return_type)

          if proof_shape?(ret_ast) do
            []
          else
            name = Keyword.get(meta, :name, "unknown")
            line = Keyword.get(meta, :line, 0)

            [
              {:proof_shape_mismatch,
               "function '#{name}' inside a proof container must return Eq(...) or a refinement type (E026)",
               line: line}
            ]
          end

        _ ->
          []
      end)

    case {base_result, shape_errors} do
      {{:ok, _}, []} ->
        {:ok, :proof_ok}

      {{:ok, _}, errs} ->
        {:error, errs}

      {{:error, base_errs}, extra} ->
        {:error, base_errs ++ extra}
    end
  end

  # A return-type AST is proof-shaped when it mentions `Eq(...)` or is a
  # refinement annotation. We stay permissive to avoid false positives on
  # newer dependent-type surface syntax.
  defp proof_shape?({:function_call, meta, _}) do
    Keyword.get(meta, :name, "") == "Eq"
  end

  defp proof_shape?({:type_annotation, meta, _}) do
    Keyword.get(meta, :refinement, false)
  end

  defp proof_shape?({:variable, _, name}) when is_binary(name) do
    name in ["Eq", "Refl", "Proof"]
  end

  defp proof_shape?(_), do: false

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
            line = Keyword.get(meta, :line, 0)

            field_map =
              Enum.reduce(body, %{}, fn
                {:param, pmeta, field_name}, acc ->
                  type_ast = Keyword.get(pmeta, :type)
                  Map.put(acc, field_name, Type.resolve(type_ast))

                _, acc ->
                  acc
              end)

            # v0.19.0: verify each field default's inferred type against
            # the declared field type (E028).
            Enum.each(body, fn
              {:param, pmeta, field_name} ->
                case Keyword.get(pmeta, :default) do
                  nil ->
                    :ok

                  default_ast ->
                    declared = Map.get(field_map, field_name, :any)
                    verify_record_default(name, field_name, default_ast, declared, env, line)
                end

              _ ->
                :ok
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

        # Bind pattern variables (v0.21.0: route every pattern through
        # `bind_pattern_vars/3` so structured patterns such as binary
        # literals `<<a, rest::binary>>`, tuples `%[x, y]`, cons
        # `[h | t]`, and ADT constructors `Ok(v)` introduce their
        # inner variables instead of being silently dropped).
        clause_env =
          Enum.reduce(params, clause_env, fn pattern, e ->
            bind_pattern_vars(e, pattern, :any)
          end)

        # The flat param_info list still drives guard refinement.
        param_info =
          Enum.flat_map(params, fn
            {:variable, _, vname} -> [{vname, :any}]
            _ -> []
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
  #
  # v0.21.0: `let` now supports in-place destructuring with the same depth
  # and exhaustiveness guarantees as `match` arms. The LHS pattern is
  # bound through `bind_pattern_vars/3` (shared with `match`), so
  # `let Ok(x) = expr`, `let %[a, b] = pair`, `let [h | t] = xs`, and
  # `let Point{x, y} = p` all introduce the right bindings with the
  # right narrowed types. Non-exhaustive destructurings surface as
  # code `E034` warnings (not errors) -- the match still compiles and
  # raises at runtime if the pattern fails, matching Erlang's `=` semantics.
  # A `let` annotated with `partial: true` in its metadata suppresses
  # the warning.
  defp do_infer(env, {:assignment, meta, [pattern, value]}) do
    annotation_ast = Keyword.get(meta, :type_annotation)
    line = Keyword.get(meta, :line, 1)

    with {:ok, val_type, env} <- do_infer(env, value) do
      if annotation_ast do
        declared = Type.resolve(annotation_ast)

        if Type.subtype?(val_type, declared) do
          env = bind_pattern_vars(env, pattern, declared)
          maybe_warn_let_non_exhaustive(pattern, declared, meta, line)
          {:ok, declared, env}
        else
          {:error,
           {:type_mismatch, "let annotation expects #{Type.display(declared)}, got #{Type.display(val_type)}",
            line: line}}
        end
      else
        env = bind_pattern_vars(env, pattern, val_type)
        maybe_warn_let_non_exhaustive(pattern, val_type, meta, line)
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

      # Run exhaustiveness check (flat fast-path)
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

      # Nested Maranget-style pass for tuple/record scrutinees.
      case PatternChecker.check_nested(scrut_type, patterns) do
        {:non_exhaustive, missing} ->
          line = Keyword.get(meta, :line, 1)

          warning =
            {:non_exhaustive_match,
             "match expression has nested non-exhaustive cases (E025), missing: #{Enum.join(missing, ", ")}",
             line: line}

          Events.emit(:type_checker, :type_warning, warning, Events.meta("nofile", line))

        _ ->
          :ok
      end

      # v0.21.0: binary-pattern exhaustiveness. Only reports when the
      # scrutinee is a Bitstring (or a refinement of it); all other
      # scrutinee types return `:exhaustive` immediately from
      # `check_binary_exhaustiveness/2` and fall through to no-op.
      case PatternChecker.check_binary_exhaustiveness(scrut_type, patterns) do
        {:non_exhaustive, missing} ->
          line = Keyword.get(meta, :line, 1)

          warning =
            {:binary_not_exhaustive, "binary match is not exhaustive (E031), missing: #{Enum.join(missing, ", ")}",
             line: line}

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

    # v0.20.0: comment nodes are trivia for type inference. Strip them so
    # a trailing comment inside a block does not steal the block's result
    # type and so an otherwise-empty block stays `:unit`.
    exprs =
      Enum.reject(exprs, fn
        {:comment, _, _} -> true
        _ -> false
      end)

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
        # The empty list is polymorphic: typing it as `{:list, :never}`
        # makes it a subtype of every `{:list, T}`, so match arms like
        # `[] -> []` compose cleanly with cons arms of a concrete type.
        {:ok, {:list, :never}, env}

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
  #
  # v0.22.0: comprehensions carry `:generator`, `:binary_generator`, and
  # `:filter` qualifiers. The body's type is inferred in an environment
  # that has the generator variables bound (via `bind_pattern_vars/3`).
  # Filters and unknown qualifiers thread the environment through but
  # do not bind anything new. The comprehension result type is always
  # `{:list, body_type}` (binary generators iterate over a bitstring
  # source but still yield a list).

  defp do_infer(env, {:comprehension, _meta, [body | qualifiers]}) do
    body_env = Enum.reduce(qualifiers, env, &bind_qualifier_vars(&2, &1))

    case do_infer(body_env, body) do
      {:ok, bt, _} -> {:ok, {:list, bt}, env}
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

  # v0.20.0: plain `#` comment nodes produced when the lexer is run with
  # `preserve_comments: true`. They are trivia from a typing standpoint:
  # report `:unit` so a trailing comment inside a block does not steal
  # the block's result type.
  defp do_infer(env, {:comment, _meta, _text}), do: {:ok, :unit, env}

  # -- assert_type (v0.19.0) ----------------------------------------------------

  defp do_infer(env, {:assert_type, meta, [expr, type_ast]}) do
    line = Keyword.get(meta, :line, 1)
    expected = Type.resolve(type_ast)

    case do_infer(env, expr) do
      {:ok, actual, env} ->
        if expected == :any or Type.subtype?(actual, expected) do
          {:ok, expected, env}
        else
          {:error,
           {:type_mismatch, "assert_type expected #{Type.display(expected)}, got #{Type.display(actual)} (E027)",
            line: line}}
        end

      err ->
        err
    end
  end

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

  defp bind_qualifier_vars(env, {:generator, _, [pattern, collection]}) do
    elem_type =
      case do_infer(env, collection) do
        {:ok, {:list, t}, _} -> t
        _ -> :any
      end

    bind_pattern_vars(env, pattern, elem_type)
  end

  defp bind_qualifier_vars(env, {:binary_generator, _, [pattern, _source]}) do
    # Binary generator patterns carry their own segment types via
    # `:bin_segment` meta; `bind_pattern_vars/3` already narrows each
    # segment variable from the specifier's `:type` entry.
    bind_pattern_vars(env, pattern, :bitstring)
  end

  defp bind_qualifier_vars(env, _), do: env

  defp resolve_record_field(env, {:named, rec_name}, field_name) do
    case Env.lookup_type(env, rec_name) do
      {:ok, {:record, _, field_map}} -> Map.get(field_map, field_name, :any)
      _ -> :any
    end
  end

  defp resolve_record_field(_env, _type, _field_name), do: :any

  # v0.19.0: check that a record default's inferred type fits the declared
  # field type. Emits `E028` when it doesn't.
  defp verify_record_default(rec_name, field_name, default_ast, declared, env, line) do
    case do_infer(env, default_ast) do
      {:ok, inferred, _} ->
        if declared == :any or Type.subtype?(inferred, declared) do
          :ok
        else
          Events.emit(
            :type_checker,
            :type_warning,
            {:record_default_mismatch,
             "record '#{rec_name}' field '#{field_name}' default has type " <>
               "#{Type.display(inferred)} but the field is declared #{Type.display(declared)} (E028)", line: line},
            Events.meta("nofile", line)
          )
        end

      _ ->
        :ok
    end
  end

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

  # Recursively bind all variables introduced by a match arm or `let`
  # pattern.
  #
  # Threads the scrutinee type through the pattern so every leaf variable
  # picks up the most precise type the structure allows. Supports:
  #
  # * wildcard (`_`) and `_name` -- no binding / bind without tracking
  # * named variable -- extend env with the narrowed type
  # * literals -- no-op
  # * tuples -- zip children with tuple element types when available
  # * lists (fixed and cons) -- use the list element type for items
  # * maps -- use record field types (if the scrutinee is a record) or
  #   the map value type; literal keys only
  # * records (`{:function_call, [record: true], ...}`) -- resolve each
  #   field's declared type from the record schema
  # * ADT constructors -- delegate to variant argument types if known,
  #   otherwise fall back to `:any`
  # * pin (`^x`) -- do not bind; the existing type stays in scope
  #
  # v0.20.0: the workhorse logic moved into
  # `Cure.Types.PatternRefinement.narrow/2` so it can also expose a
  # narrowed scrutinee type (for disjoint-tag or literal-equality
  # witnesses). The function below is a thin wrapper that extends
  # the environment with the bindings returned by the narrower and
  # preserves the existing behaviour for record patterns, where the
  # schema-aware binding in `bind_record_pattern/3` provides richer
  # per-field types than `PatternRefinement` currently does.
  defp bind_pattern_vars(env, nil, _type), do: env
  defp bind_pattern_vars(env, {:variable, _, "_"}, _type), do: env
  defp bind_pattern_vars(env, {:variable, _, "_" <> _}, _type), do: env
  defp bind_pattern_vars(env, {:variable, _, name}, type), do: Env.extend(env, name, type)

  # v0.21.0: binary literal patterns `<<seg1, seg2, ...>>` are emitted
  # by the parser as `{:literal, [subtype: :bytes, ...], segments}`.
  # Recurse into every `{:bin_segment, meta, [value]}` so the segment
  # variables (e.g. `b` in `<<b, rest::binary>>`) pick up the correct
  # types from the segment's `:type` meta. An empty segment list is the
  # literal `<<>>` which binds nothing.
  defp bind_pattern_vars(env, {:literal, meta, segments}, _type) do
    case Keyword.get(meta, :subtype) do
      :bytes when is_list(segments) ->
        Enum.reduce(segments, env, fn seg, e ->
          bind_pattern_vars(e, seg, bin_segment_type(seg))
        end)

      _ ->
        env
    end
  end

  # The bin_segment AST carries the segment's variable/literal in its
  # children and the specifier meta (`:type`, `:size`, `:unit`,
  # `:signedness`, `:endianness`) on the meta. Recurse into the
  # child with the inferred segment type so the variable binds to
  # the right scalar/bitstring type.
  defp bind_pattern_vars(env, {:bin_segment, _meta, [inner]}, type) do
    bind_pattern_vars(env, inner, type)
  end

  defp bind_pattern_vars(env, {:pin, _, _}, _type), do: env

  defp bind_pattern_vars(env, {:unary_op, _, [inner]}, type),
    do: bind_pattern_vars(env, inner, type)

  # For non-record/non-function_call compound patterns, defer to the
  # PatternRefinement module. It produces a bindings map whose types
  # are `:any` by default; we re-walk the structure for tuples/lists/
  # maps via the original recursion below to preserve the more
  # precise element typing.

  defp bind_pattern_vars(env, {:list, meta, elems}, type) do
    elem_type = list_element_type(type)

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

  defp bind_pattern_vars(env, {:tuple, _, elems}, type) do
    case type do
      {:tuple, types} when is_list(types) and length(types) == length(elems) ->
        Enum.zip(elems, types)
        |> Enum.reduce(env, fn {el, t}, e -> bind_pattern_vars(e, el, t) end)

      _ ->
        Enum.reduce(elems, env, &bind_pattern_vars(&2, &1, :any))
    end
  end

  defp bind_pattern_vars(env, {:map, _, pairs}, type) do
    Enum.reduce(pairs, env, fn
      {:pair, _, [key, value_pat]}, e ->
        value_type = resolve_map_value_type(env, type, key)
        bind_pattern_vars(e, value_pat, value_type)

      _, e ->
        e
    end)
  end

  defp bind_pattern_vars(env, {:function_call, meta, args} = pat, type) do
    cond do
      Keyword.get(meta, :record, false) ->
        bind_record_pattern(env, meta, args)

      constructor?(Keyword.get(meta, :name)) ->
        bind_constructor_pattern(env, pat, type)

      true ->
        Enum.reduce(args, env, &bind_pattern_vars(&2, &1, :any))
    end
  end

  defp bind_pattern_vars(env, _, _type), do: env

  defp list_element_type({:list, t}), do: t
  defp list_element_type(_), do: :any

  # Map a `{:bin_segment, meta, ...}` specifier to the scalar type the
  # segment binds. The default specifier (`integer-unsigned-big-size(8)`)
  # yields `:int`; `:utf8`/`:utf16`/`:utf32` yield `:char` (the code
  # point); `:binary`/`:bytes`/`:bitstring`/`:bits` yield `:bitstring`;
  # `:float` yields `:float`. Anything unknown falls back to `:any`.
  defp bin_segment_type({:bin_segment, meta, _}) do
    case Keyword.get(meta, :type, :integer) do
      :integer -> :int
      :float -> :float
      :utf8 -> :char
      :utf16 -> :char
      :utf32 -> :char
      :binary -> :bitstring
      :bytes -> :bitstring
      :bitstring -> :bitstring
      :bits -> :bitstring
      _ -> :any
    end
  end

  defp bin_segment_type(_), do: :any

  defp resolve_map_value_type(env, type, key) do
    field_name =
      case key do
        {:literal, [subtype: :symbol], atom} when is_atom(atom) -> Atom.to_string(atom)
        {:literal, [subtype: :symbol, _: _], atom} when is_atom(atom) -> Atom.to_string(atom)
        _ -> nil
      end

    cond do
      field_name != nil ->
        resolve_record_field(env, type, field_name)

      match?({:map, _, _}, type) ->
        {_, _, vt} = type
        vt

      true ->
        :any
    end
  end

  defp bind_record_pattern(env, meta, args) do
    rec_name = Keyword.get(meta, :name, "")

    {known_fields, line} =
      case Env.lookup_type(env, rec_name) do
        {:ok, {:record, _, field_map}} -> {field_map, Keyword.get(meta, :line, 0)}
        _ -> {%{}, Keyword.get(meta, :line, 0)}
      end

    Enum.reduce(args, env, fn arg, e ->
      case arg do
        # field punning shorthand: `x` inside `Point{x}` binds to field `x`.
        {:variable, _, name} when is_binary(name) and name != "_" ->
          type = Map.get(known_fields, name, :any)

          if known_fields != %{} and not Map.has_key?(known_fields, name) do
            emit_record_warning(e, rec_name, name, line)
          end

          Env.extend(e, name, type)

        {:pair, _, [key, value_pat]} ->
          field_name =
            case key do
              {:literal, [subtype: :symbol], atom} when is_atom(atom) -> Atom.to_string(atom)
              _ -> nil
            end

          type =
            case field_name do
              nil -> :any
              fname -> Map.get(known_fields, fname, :any)
            end

          if field_name != nil and known_fields != %{} and not Map.has_key?(known_fields, field_name) do
            emit_record_warning(e, rec_name, field_name, line)
          end

          bind_pattern_vars(e, value_pat, type)

        _ ->
          e
      end
    end)
  end

  defp bind_constructor_pattern(env, {:function_call, _meta, args}, _type) do
    # Without a resolved ADT variant registry we cannot narrow each argument's
    # type, so fall back to `:any`. The compiler still benefits from binding
    # the variable names.
    Enum.reduce(args, env, &bind_pattern_vars(&2, &1, :any))
  end

  defp emit_record_warning(env, rec_name, field, line) do
    if Map.get(env, :emit_events, false) do
      file = Map.get(env, :file, "nofile")

      Events.emit(
        :type_checker,
        :type_warning,
        {:unknown_record_field, "record '#{rec_name}' pattern references unknown field '#{field}' (E021)", line: line},
        Events.meta(file, line)
      )
    end

    :ok
  end

  defp constructor?(name) when is_binary(name) do
    case String.first(name) do
      nil -> false
      first -> first == String.upcase(first) and first != String.downcase(first)
    end
  end

  defp constructor?(_), do: false

  # -- Let Exhaustiveness (v0.21.0) -------------------------------------------

  # Single-arm exhaustiveness gate for `let` bindings.
  #
  # A plain-variable or wildcard LHS is trivially exhaustive and exits the
  # pattern-checker fast path. Structured LHS patterns (ADT constructors,
  # tuples, lists, records, maps, binaries) are classified through the
  # existing `PatternChecker` so the message format matches `match`
  # non-exhaustiveness. The warning is tagged `E034` so `cure explain E034`
  # describes the fix. A `let` whose metadata carries `partial: true`
  # suppresses the warning.
  defp maybe_warn_let_non_exhaustive(pattern, scrut_type, meta, line) do
    cond do
      Keyword.get(meta, :partial, false) ->
        :ok

      trivially_exhaustive_let?(pattern) ->
        :ok

      true ->
        case PatternChecker.check_match(scrut_type, [pattern]) do
          {:non_exhaustive, missing} ->
            warning =
              {:let_not_exhaustive,
               "let binding pattern is not exhaustive (E034), missing: #{Enum.join(missing, ", ")}", line: line}

            Events.emit(:type_checker, :type_warning, warning, Events.meta("nofile", line))

          _ ->
            :ok
        end
    end
  end

  defp trivially_exhaustive_let?({:variable, _, _}), do: true
  defp trivially_exhaustive_let?(_), do: false

  defp extract_line({_, meta, _}) when is_list(meta), do: Keyword.get(meta, :line, 1)
  defp extract_line(_), do: 1
end
