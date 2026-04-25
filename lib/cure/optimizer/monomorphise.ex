defmodule Cure.Optimizer.Monomorphise do
  @moduledoc """
  Monomorphisation pass for the Cure optimiser.

  Specialises polymorphic functions whose call sites all use concrete
  types. Adds the v0.31.0 perf primitive: every call site that pins
  every type variable to a concrete type gets its own specialised
  clone, named `original__<6-hex-hash-of-substitution>`. The original
  generic `function_def` is **never dropped**; out-of-unit callers
  (cross-module calls, protocol-registry dispatch, dynamic
  `apply/3`) keep working unchanged.

  ## Algorithm

  1. **Collect** -- walk the module body, identify
     `{:function_def, meta, body}` nodes whose declared signature
     (resolved via `Cure.Types.Type.resolve/1`) mentions at least one
     `{:type_var, _}` and which are not `@extern`.
  2. **Discover** -- walk every `{:function_call, _, args}` node.
     For each call into a known-polymorphic local function, infer
     concrete argument types via a self-contained lightweight oracle
     (see `Cure.Optimizer.Monomorphise.Oracle`). Unify with the
     formal parameter types via `Cure.Types.Unify.unify_many/1`. Drop
     call sites where the substitution still contains type variables
     or unresolved `:any`.
  3. **Materialise** -- for each unique substitution, produce one
     specialised `function_def` clone. Rewrite the call site's
     `:name` meta to point at the mangled clone.
  4. **Substitute interior calls** -- inside every materialised
     specialisation, rewrite intra-unit polymorphic calls so that
     `id(x)` inside `map_int` becomes `id__<hash>(x)` whenever the
     interior call's arguments solve to the same concrete shape as
     the enclosing specialisation.

  ## Budget

  Per-function soft cap of **16 specialisations**. When exceeded, the
  pass keeps the first 16 unique specialisations, falls back to the
  generic clone for the rest, emits the
  `:monomorph_budget_exceeded` pipeline event, and the type checker
  surfaces a warning under code **E064 Monomorphisation Budget
  Exhausted**.

  Tunable via `[compiler].monomorph_budget` in `Cure.toml` and the
  `:monomorph_budget` keyword on `Cure.Optimizer.optimize/2`.

  ## Pipeline events

  * `{:type_checker, :monomorph_specialised, {name, arity, subst, mangled}, meta}`
  * `{:type_checker, :monomorph_skipped, {name, arity, reason}, meta}`
    where `reason` is `:not_polymorphic | :partial_solution | :budget_exhausted`
  """

  alias Cure.Pipeline.Events
  alias Cure.Types.{Type, Unify}

  @default_budget 16

  @doc """
  Run the monomorphisation pass.

  Returns `{ast, count}` where `count` is the number of
  specialisations materialised. The shape mirrors every other
  optimiser pass.

  Accepts an optional keyword:
  * `:budget` -- soft cap on specialisations per source function
    (defaults to `#{@default_budget}`).
  * `:emit_events` -- emit pipeline events (default `true`).
  * `:file` -- file path for event metadata (default `"nofile"`).
  """
  @spec run(tuple()) :: {tuple(), non_neg_integer()}
  def run(ast), do: run(ast, [])

  @spec run(tuple(), keyword()) :: {tuple(), non_neg_integer()}
  def run(ast, opts) do
    budget = Keyword.get(opts, :budget, @default_budget)
    emit? = Keyword.get(opts, :emit_events, true)
    file = Keyword.get(opts, :file, "nofile")

    case ast do
      {:container, meta, body} ->
        case Keyword.get(meta, :container_type) do
          :module -> monomorphise_module(meta, body, budget, emit?, file)
          _ -> {ast, 0}
        end

      {:block, meta, children} ->
        case Enum.find_index(children, &module_container?/1) do
          nil ->
            {ast, 0}

          idx ->
            container = Enum.at(children, idx)
            {:container, c_meta, c_body} = container
            {new_container, count} = monomorphise_module(c_meta, c_body, budget, emit?, file)
            new_children = List.replace_at(children, idx, new_container)
            {{:block, meta, new_children}, count}
        end

      _ ->
        {ast, 0}
    end
  end

  defp module_container?({:container, m, _}) when is_list(m), do: Keyword.get(m, :container_type) == :module
  defp module_container?(_), do: false

  # -- Phase orchestration ----------------------------------------------------

  defp monomorphise_module(meta, body, budget, emit?, file) do
    sigs = collect_signatures(body)
    polymorphics = polymorphic_signatures(sigs)

    if map_size(polymorphics) == 0 do
      {{:container, meta, body}, 0}
    else
      # Phase 2: walk every call site, gather solved substitutions.
      raw_call_sites = collect_call_sites(body, polymorphics, sigs)

      # Phase 3: budget the specialisations and build the substitution
      # registry: %{name => %{arity => [{subst, mangled} ...]}}.
      {registry, budget_overflows} = budget_specialisations(raw_call_sites, budget)

      # Phase 4: rewrite every call site that resolved to a registered
      # specialisation, *and* materialise the new function_defs.
      {rewritten_body, rewrite_count} =
        rewrite_call_sites(body, registry, polymorphics, sigs)

      specialised_defs = materialise_specialisations(body, registry, polymorphics)

      new_body = rewritten_body ++ specialised_defs

      if emit? do
        emit_specialised_events(registry, file)
        emit_overflow_events(budget_overflows, file)
      end

      total = rewrite_count

      {{:container, meta, new_body}, total}
    end
  end

  # -- Phase 1: collect signatures --------------------------------------------

  @doc false
  def collect_signatures(body) when is_list(body) do
    Enum.reduce(body, %{}, fn
      {:function_def, meta, _body}, acc ->
        if Keyword.get(meta, :extern) != nil do
          acc
        else
          name = Keyword.get(meta, :name, "")
          params = Keyword.get(meta, :params, [])
          arity = length(params)
          ret_ast = Keyword.get(meta, :return_type)

          param_types =
            Enum.map(params, fn {:param, pmeta, _pname} ->
              Type.resolve(Keyword.get(pmeta, :type))
            end)

          param_names =
            Enum.map(params, fn {:param, _pmeta, pname} -> pname end)

          ret_type = if ret_ast, do: Type.resolve(ret_ast), else: :any

          Map.put(acc, {name, arity}, %{
            param_types: param_types,
            param_names: param_names,
            ret_type: ret_type,
            meta: meta
          })
        end

      _, acc ->
        acc
    end)
  end

  defp polymorphic_signatures(sigs) do
    Enum.filter(sigs, fn {_key, %{param_types: ps, ret_type: r}} ->
      Enum.any?(ps, &has_type_var?/1) or has_type_var?(r)
    end)
    |> Map.new()
  end

  defp has_type_var?({:type_var, _}), do: true
  defp has_type_var?({:list, t}), do: has_type_var?(t)
  defp has_type_var?({:tuple, ts}), do: Enum.any?(ts, &has_type_var?/1)
  defp has_type_var?({:fun, ps, r}), do: Enum.any?(ps, &has_type_var?/1) or has_type_var?(r)
  defp has_type_var?({:effun, ps, r, _}), do: Enum.any?(ps, &has_type_var?/1) or has_type_var?(r)
  defp has_type_var?({:adt, _, ps}), do: Enum.any?(ps, &has_type_var?/1)
  defp has_type_var?({:map, k, v}), do: has_type_var?(k) or has_type_var?(v)
  defp has_type_var?({:refinement, base, _, _}), do: has_type_var?(base)
  defp has_type_var?({:pid, t}), do: has_type_var?(t)
  defp has_type_var?(_), do: false

  # -- Phase 2: discover call sites -------------------------------------------

  # Walk the AST collecting `{name, arity, subst}` triples where the
  # substitution successfully solved every formal type variable to a
  # concrete (non-`:any`, non-`{:type_var, _}`) type. Variable arguments
  # whose type cannot be inferred locally cause us to skip the call.
  defp collect_call_sites(body, polymorphics, sigs) do
    body
    |> Enum.flat_map(&do_collect_calls(&1, polymorphics, sigs))
  end

  defp do_collect_calls({:function_call, meta, args}, polys, sigs) do
    nested = Enum.flat_map(args, &do_collect_calls(&1, polys, sigs))

    name = Keyword.get(meta, :name, "")
    is_record? = Keyword.get(meta, :record, false)

    if is_record? do
      nested
    else
      arity = length(args)

      case Map.get(polys, {name, arity}) do
        nil ->
          nested

        %{param_types: ptypes} ->
          arg_types = Enum.map(args, &infer_arg_type(&1, sigs))

          if Enum.any?(arg_types, &skip?/1) do
            nested
          else
            case Unify.unify_many(Enum.zip(ptypes, arg_types)) do
              {:ok, subst, _trace} ->
                if subst_concrete?(subst) do
                  [{name, arity, subst} | nested]
                else
                  nested
                end

              _ ->
                nested
            end
          end
      end
    end
  end

  defp do_collect_calls({:function_def, _meta, body}, polys, sigs) when is_list(body) do
    Enum.flat_map(body, &do_collect_calls(&1, polys, sigs))
  end

  defp do_collect_calls({:container, _meta, body}, polys, sigs) when is_list(body) do
    Enum.flat_map(body, &do_collect_calls(&1, polys, sigs))
  end

  defp do_collect_calls({:block, _meta, children}, polys, sigs) when is_list(children) do
    Enum.flat_map(children, &do_collect_calls(&1, polys, sigs))
  end

  defp do_collect_calls({_tag, _meta, children}, polys, sigs) when is_list(children) do
    Enum.flat_map(children, &do_collect_calls(&1, polys, sigs))
  end

  defp do_collect_calls(_, _polys, _sigs), do: []

  # `:skip` is a sentinel: the argument's type could not be inferred
  # locally and we should not attempt to specialise this call site.
  defp skip?(:skip), do: true
  defp skip?(_), do: false

  defp subst_concrete?(subst) do
    Enum.all?(subst, fn {_k, t} -> not has_type_var?(t) end)
  end

  # -- Lightweight type oracle (call-site arg inference) ----------------------

  @doc false
  def infer_arg_type({:literal, meta, value}, _sigs) do
    case Keyword.get(meta, :subtype) do
      :integer ->
        :int

      :float ->
        :float

      :boolean ->
        :bool

      :string ->
        :string

      :atom ->
        :atom

      :char ->
        :char

      :bytes ->
        :string

      _ ->
        cond do
          is_integer(value) -> :int
          is_float(value) -> :float
          is_boolean(value) -> :bool
          is_binary(value) -> :string
          is_atom(value) -> :atom
          true -> :any
        end
    end
  end

  def infer_arg_type({:list, meta, elems}, sigs) do
    cons? = Keyword.get(meta, :cons, false)

    cond do
      elems == [] ->
        {:list, :never}

      cons? ->
        [head | _] = elems
        {:list, infer_arg_type(head, sigs)}

      true ->
        elem_types = Enum.map(elems, &infer_arg_type(&1, sigs))

        if Enum.any?(elem_types, &skip?/1) do
          :skip
        else
          joined = Enum.reduce(elem_types, :never, &Type.join/2)
          {:list, joined}
        end
    end
  end

  def infer_arg_type({:tuple, _meta, elems}, sigs) do
    types = Enum.map(elems, &infer_arg_type(&1, sigs))

    if Enum.any?(types, &skip?/1) do
      :skip
    else
      {:tuple, types}
    end
  end

  def infer_arg_type({:map, _meta, _pairs}, _sigs), do: {:map, :any, :any}

  def infer_arg_type({:lambda, meta, _body}, _sigs) do
    params = Keyword.get(meta, :params, [])

    param_types =
      Enum.map(params, fn {:param, pmeta, _pname} ->
        case Keyword.get(pmeta, :type) do
          nil -> :any
          ast -> Type.resolve(ast)
        end
      end)

    {:fun, param_types, :any}
  end

  # PascalCase function calls flagged as record constructions are
  # the only `function_call` form whose return type we can infer
  # without a real type environment.
  def infer_arg_type({:function_call, meta, args}, sigs) do
    name = Keyword.get(meta, :name, "")
    is_record? = Keyword.get(meta, :record, false)
    arity = length(args)

    cond do
      is_record? ->
        {:named, name}

      true ->
        case Map.get(sigs, {name, arity}) do
          nil ->
            :skip

          %{ret_type: ret} ->
            if has_type_var?(ret), do: :skip, else: ret
        end
    end
  end

  # Variable references are the most common reason we cannot infer
  # without a real type environment. Skipping is the safe choice.
  def infer_arg_type({:variable, _, _}, _sigs), do: :skip

  # Other compound forms -- conditional, comprehension, send, etc. --
  # are intentionally treated as "unknown" for the optimiser's
  # purposes. They fall through to `:skip` so we do not synthesise an
  # ill-grounded specialisation.
  def infer_arg_type(_, _sigs), do: :skip

  # -- Phase 3: budget specialisations ----------------------------------------

  # Returns `{registry, overflows}` where:
  #   registry :: %{ {name, arity} => %{subst_key => mangled} }
  #   overflows :: [{name, arity, count}]
  defp budget_specialisations(call_sites, budget) do
    grouped =
      Enum.group_by(call_sites, fn {name, arity, _subst} -> {name, arity} end, fn {_n, _a, subst} -> subst end)

    Enum.reduce(grouped, {%{}, []}, fn {{name, arity}, substs}, {reg, over} ->
      uniq = Enum.uniq_by(substs, &subst_key/1)

      cond do
        length(uniq) <= budget ->
          inner = build_specialisation_map(uniq, name)
          {Map.put(reg, {name, arity}, inner), over}

        true ->
          taken = Enum.take(uniq, budget)
          dropped = length(uniq) - budget
          inner = build_specialisation_map(taken, name)
          {Map.put(reg, {name, arity}, inner), [{name, arity, dropped} | over]}
      end
    end)
  end

  defp build_specialisation_map(substs, name) do
    Enum.reduce(substs, %{}, fn subst, acc ->
      key = subst_key(subst)
      mangled = mangled_name(name, key)
      Map.put(acc, key, %{subst: subst, mangled: mangled})
    end)
  end

  defp subst_key(subst) do
    subst
    |> Enum.sort()
    |> Enum.map(fn {var, t} -> {var, canonicalise(t)} end)
  end

  # Strip metadata that does not affect the type's operational shape
  # so two structurally-equal substitutions produce the same key
  # regardless of where they came from.
  defp canonicalise({:list, t}), do: {:list, canonicalise(t)}
  defp canonicalise({:tuple, ts}), do: {:tuple, Enum.map(ts, &canonicalise/1)}

  defp canonicalise({:fun, ps, r}),
    do: {:fun, Enum.map(ps, &canonicalise/1), canonicalise(r)}

  defp canonicalise({:effun, ps, r, effs}),
    do: {:effun, Enum.map(ps, &canonicalise/1), canonicalise(r), effs}

  defp canonicalise({:adt, n, ps}), do: {:adt, n, Enum.map(ps, &canonicalise/1)}
  defp canonicalise({:map, k, v}), do: {:map, canonicalise(k), canonicalise(v)}
  defp canonicalise({:refinement, base, var, _pred}), do: {:refinement, canonicalise(base), var, :erased}
  defp canonicalise({:pid, t}), do: {:pid, canonicalise(t)}
  defp canonicalise(other), do: other

  defp mangled_name(name, key) do
    hash = :erlang.phash2(key) |> rem(16_777_216)
    suffix = hash |> Integer.to_string(16) |> String.downcase() |> String.pad_leading(6, "0")
    name <> "__" <> suffix
  end

  # -- Phase 4: rewrite call sites + materialise specialisations --------------

  defp rewrite_call_sites(body, registry, polymorphics, sigs) do
    Enum.map_reduce(body, 0, fn node, count ->
      do_rewrite(node, registry, polymorphics, sigs, count)
    end)
  end

  defp do_rewrite({:function_call, meta, args}, registry, polymorphics, sigs, count) do
    {new_args, count} =
      Enum.map_reduce(args, count, fn arg, c ->
        do_rewrite(arg, registry, polymorphics, sigs, c)
      end)

    name = Keyword.get(meta, :name, "")
    is_record? = Keyword.get(meta, :record, false)
    arity = length(args)

    cond do
      is_record? ->
        {{:function_call, meta, new_args}, count}

      true ->
        case Map.get(registry, {name, arity}) do
          nil ->
            {{:function_call, meta, new_args}, count}

          inner ->
            # Re-derive the call's substitution by unifying the formal
            # parameter types of the polymorphic original against the
            # inferred argument types. This picks the *correct*
            # specialisation when several substitutions share a hash
            # bucket but differ in variable assignment
            # (e.g. `pair_first(Int, String)` vs `(String, Int)`).
            case Map.get(polymorphics, {name, arity}) do
              nil ->
                {{:function_call, meta, new_args}, count}

              %{param_types: ptypes} ->
                arg_types = Enum.map(new_args, &infer_arg_type(&1, sigs))

                case derive_subst_key(ptypes, arg_types) do
                  {:ok, key} ->
                    case Map.get(inner, key) do
                      %{mangled: mangled} ->
                        new_meta = Keyword.put(meta, :name, mangled)
                        {{:function_call, new_meta, new_args}, count + 1}

                      _ ->
                        {{:function_call, meta, new_args}, count}
                    end

                  :error ->
                    {{:function_call, meta, new_args}, count}
                end
            end
        end
    end
  end

  defp do_rewrite({:function_def, meta, body}, registry, polymorphics, sigs, count) do
    {new_body, count} =
      Enum.map_reduce(body, count, fn n, c ->
        do_rewrite(n, registry, polymorphics, sigs, c)
      end)

    {{:function_def, meta, new_body}, count}
  end

  defp do_rewrite({:container, meta, body}, registry, polymorphics, sigs, count) do
    {new_body, count} =
      Enum.map_reduce(body, count, fn n, c ->
        do_rewrite(n, registry, polymorphics, sigs, c)
      end)

    {{:container, meta, new_body}, count}
  end

  defp do_rewrite({:block, meta, children}, registry, polymorphics, sigs, count) do
    {new_children, count} =
      Enum.map_reduce(children, count, fn n, c ->
        do_rewrite(n, registry, polymorphics, sigs, c)
      end)

    {{:block, meta, new_children}, count}
  end

  defp do_rewrite({tag, meta, children}, registry, polymorphics, sigs, count) when is_list(children) do
    {new_children, count} =
      Enum.map_reduce(children, count, fn n, c ->
        do_rewrite(n, registry, polymorphics, sigs, c)
      end)

    {{tag, meta, new_children}, count}
  end

  defp do_rewrite(node, _registry, _polymorphics, _sigs, count), do: {node, count}

  defp derive_subst_key(ptypes, arg_types) do
    if Enum.any?(arg_types, &(&1 == :skip)) do
      :error
    else
      case Unify.unify_many(Enum.zip(ptypes, arg_types)) do
        {:ok, subst, _trace} ->
          if subst_concrete?(subst) do
            {:ok, subst_key(subst)}
          else
            :error
          end

        _ ->
          :error
      end
    end
  end

  # Build specialised function_defs by cloning each polymorphic original
  # under each registered substitution. Type variables in `:param` meta
  # `:type` ASTs are left intact: `Cure.Types.Checker` already treats
  # them as universally compatible (`subtype?({:type_var, _}, _)` is
  # always true), so the BEAM forms compile and run identically. The
  # *function-call rewriting* is what actually delivers the perf win:
  # every call to the specialisation site goes to the mangled clone,
  # and a future pass can do further per-clone simplification.
  defp materialise_specialisations(body, registry, polymorphics) do
    Enum.flat_map(body, fn
      {:function_def, meta, fn_body} = orig ->
        name = Keyword.get(meta, :name, "")
        arity = length(Keyword.get(meta, :params, []))

        if Map.has_key?(polymorphics, {name, arity}) do
          case Map.get(registry, {name, arity}) do
            nil ->
              []

            inner ->
              Enum.map(inner, fn {_key, %{mangled: mangled}} ->
                # Carry a `:specialised_from` marker for tooling.
                new_meta =
                  meta
                  |> Keyword.put(:name, mangled)
                  |> Keyword.put(:specialised_from, name)
                  |> Keyword.put(:visibility, :private)

                {:function_def, new_meta, fn_body}
              end)
          end
        else
          _ = orig
          []
        end

      _ ->
        []
    end)
  end

  # -- Pipeline events --------------------------------------------------------

  defp emit_specialised_events(registry, file) do
    Enum.each(registry, fn {{name, arity}, inner} ->
      Enum.each(inner, fn {_key, %{subst: subst, mangled: mangled}} ->
        Events.emit(
          :type_checker,
          :monomorph_specialised,
          {name, arity, subst, mangled},
          Events.meta(file, 0)
        )
      end)
    end)
  end

  defp emit_overflow_events(overflows, file) do
    Enum.each(overflows, fn {name, arity, dropped} ->
      Events.emit(
        :type_checker,
        :monomorph_skipped,
        {name, arity, :budget_exhausted, dropped},
        Events.meta(file, 0)
      )

      Events.emit(
        :type_checker,
        :type_warning,
        {:monomorph_budget_exceeded,
         "monomorphisation budget exhausted for '#{name}/#{arity}': " <>
           "#{dropped} additional specialisation(s) skipped (E064)", line: 0},
        Events.meta(file, 0)
      )
    end)
  end
end
