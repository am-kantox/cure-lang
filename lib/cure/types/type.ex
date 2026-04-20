defmodule Cure.Types.Type do
  @moduledoc """
  Canonical type representations for the Cure type system.

  ## Primitive types

  Represented as atoms: `:int`, `:float`, `:string`, `:bool`, `:atom`,
  `:unit`, `:any`, `:never`, `:char`, `:regex`.

  ## Composite types

  - `{:list, element_type}`
  - `{:tuple, [type1, type2, ...]}`
  - `{:map, key_type, value_type}`
  - `{:fun, [param_types], return_type}`
  - `{:adt, name_atom, [type_params]}`
  - `{:record, name_atom, %{field_name_string => type}}` -- stored in
    `Cure.Types.Env.types`; used by the checker for field lookup
  - `{:named, name_string}` -- lightweight reference to a user-defined
    record or ADT type; produced by `resolve_name/1` for any PascalCase
    name not in the built-in set (`Int`, `String`, ...)
  - `{:type_var, id}` -- fresh unification variable (future use)
  - `{:refinement, base_type, var_name, predicate_ast}` -- structural only
  - `{:effun, [param_types], return_type, effects}` -- effectful function type

  ## Named type resolution

  `Type.resolve/1` maps parser type-expression AST nodes to canonical types.
  For unknown uppercase names (user-defined records, ADTs, type variables),
  it returns `{:named, name}` rather than `:any`. This preserves the original
  name so the type checker can look up field schemas and perform meaningful
  subtype checks.

  Built-in names (`Int`, `Float`, `String`, `Bool`, `Any`, `Never`, ...) are
  still resolved directly to their primitive atoms.

  ## Named type subtyping

  - `{:named, T} <: Any` for all T
  - `{:named, T} <: {:adt, key, _}` when `String.downcase(T) == key`
  - `{:named, T} <: {:record, key, _}` when `String.downcase(T) == key`
  - `{:named, T} <: {:named, T}` (reflexivity)

  ## Effects

  Effects are tracked as a `MapSet` of atoms from a closed set:
  `:io`, `:state`, `:exception`, `:spawn`, `:extern`.
  A pure function has `effects = MapSet.new()`.
  The plain `{:fun, ...}` tuple is treated as sugar for empty effects.
  """

  # -- Primitive Predicates ----------------------------------------------------

  @primitives [:int, :float, :string, :bool, :atom, :unit, :any, :never, :char, :regex]

  @effect_kinds [:io, :state, :exception, :spawn, :extern]

  @doc "Returns true if `t` is a primitive type atom."
  def primitive?(t) when t in @primitives, do: true
  def primitive?(_), do: false

  @doc "Returns true if `t` is a numeric type (`:int` or `:float`)."
  def numeric?(:int), do: true
  def numeric?(:float), do: true
  # Path-sensitive refinements narrow a base type; for arithmetic we only
  # care whether the underlying base is numeric.
  def numeric?({:refinement, base, _, _}), do: numeric?(base)
  def numeric?(_), do: false

  @doc "Returns the valid effect kind atoms."
  def effect_kinds, do: @effect_kinds

  @doc "Returns true if `t` is a pure function type (no effects)."
  def pure?({:fun, _, _}), do: true
  def pure?({:constrained_fun, _, _, _, _}), do: true
  def pure?({:effun, _, _, effects}), do: Enum.empty?(effects)
  def pure?(_), do: false

  @doc "Extract effects from a function type. Returns a MapSet."
  def effects({:effun, _, _, effects}), do: effects
  def effects({:fun, _, _}), do: MapSet.new()
  def effects({:constrained_fun, _, _, _, _}), do: MapSet.new()
  def effects(_), do: MapSet.new()

  @doc "Compute the join (union) of two effect sets."
  def effect_join(e1, e2), do: MapSet.union(e1, e2)

  # -- Subtyping (structural, non-recursive for Phase 1) -----------------------

  @doc """
  Returns true if `sub` is a subtype of `sup`.

  Phase 1 rules:
  - `:any` is a supertype of everything.
  - `:never` is a subtype of everything.
  - A type is a subtype of itself.
  - `:int` <: `:float` (numeric widening).
  """
  def subtype?(:never, _), do: true
  def subtype?(_, :any), do: true
  # `:any` behaves as both top and bottom in Cure's gradual type system:
  # this mirrors the permissive `a == :any or p == :any` clause that the
  # checker already uses in `params_match?/2`.
  def subtype?(:any, _), do: true
  def subtype?(_, {:type_hole, _}), do: true
  def subtype?({:type_hole, _}, _), do: true
  # Type variables are polymorphic placeholders: treat them as universally
  # compatible until proper unification is wired into `check_fn_call`.
  def subtype?({:type_var, _}, _), do: true
  def subtype?(_, {:type_var, _}), do: true
  def subtype?(t, t), do: true
  def subtype?(:int, :float), do: true
  def subtype?({:list, a}, {:list, b}), do: subtype?(a, b)

  def subtype?({:tuple, as}, {:tuple, bs}) when length(as) == length(bs) do
    Enum.zip(as, bs) |> Enum.all?(fn {a, b} -> subtype?(a, b) end)
  end

  def subtype?({:fun, pa, ra}, {:fun, pb, rb}) when length(pa) == length(pb) do
    # contravariant in params, covariant in return
    params_ok = Enum.zip(pb, pa) |> Enum.all?(fn {b, a} -> subtype?(b, a) end)
    params_ok and subtype?(ra, rb)
  end

  # Effect-annotated function subtyping
  # Pure fun is subtype of any effectful fun with same signature
  def subtype?({:fun, pa, ra}, {:effun, pb, rb, _effects}) when length(pa) == length(pb) do
    subtype?({:fun, pa, ra}, {:fun, pb, rb})
  end

  # Effectful fun is subtype of pure fun only when effect set is empty
  def subtype?({:effun, pa, ra, effects}, {:fun, pb, rb}) when length(pa) == length(pb) do
    Enum.empty?(effects) and subtype?({:fun, pa, ra}, {:fun, pb, rb})
  end

  # Effectful fun subtyping: e1 must be subset of e2
  def subtype?({:effun, pa, ra, e1}, {:effun, pb, rb, e2}) when length(pa) == length(pb) do
    MapSet.subset?(e1, e2) and subtype?({:fun, pa, ra}, {:fun, pb, rb})
  end

  # Refinement type is a subtype of its base type
  def subtype?({:refinement, base, _, _}, sup) when is_atom(sup), do: subtype?(base, sup)

  # Refinement subtype checking (delegates to SMT)
  def subtype?({:refinement, _, _, _} = sub, {:refinement, _, _, _} = sup) do
    case Cure.Types.Refinement.subtype?(sub, sup) do
      true -> true
      _ -> false
    end
  end

  # Named type (user-defined record/ADT) subtyping
  # {:named, "Pair"} is a subtype of {:adt, :pair, _} when the lowercased name matches
  def subtype?({:named, name}, {:adt, key, _params}),
    do: String.downcase(name) == Atom.to_string(key)

  def subtype?({:named, name}, {:record, key, _fields}),
    do: String.downcase(name) == Atom.to_string(key)

  def subtype?({:named, a}, {:named, b}), do: a == b

  # `Tuple` as a user-written type name resolves to `{:adt, :tuple, []}` and
  # is treated as "any tuple". Concrete tuples are subtypes of it and vice
  # versa, so `List(Tuple)` unifies with e.g. `List(%[Float, Float])`.
  def subtype?({:tuple, _}, {:adt, :tuple, _}), do: true
  def subtype?({:adt, :tuple, _}, {:tuple, _}), do: true

  # Sigma subtyping (delegates to the Sigma module)
  def subtype?({:sigma, _, _, _} = a, b), do: Cure.Types.Sigma.subtype?(a, b)
  def subtype?(a, {:sigma, _, _, _} = b), do: Cure.Types.Sigma.subtype?(a, b)

  # Equality types: invariant in T, structural on a/b after normalization
  def subtype?({:eq, t1, a1, b1}, {:eq, t2, a2, b2}) do
    subtype?(t1, t2) and subtype?(t2, t1) and a1 == a2 and b1 == b2
  end

  # v0.19.0: Eq(...) proofs are runtime-erased atoms (`:cure_refl`).
  # Any atom is therefore accepted as an inhabitant of an Eq type, which
  # lets `proof` containers return `:cure_refl` directly.
  def subtype?(:atom, {:eq, _, _, _}), do: true

  # Pi subtyping (covariant in return when params match)
  def subtype?({:pi, ps1, r1}, {:pi, ps2, r2}) when length(ps1) == length(ps2) do
    Enum.zip(ps1, ps2)
    |> Enum.all?(fn {{_, t1, m1}, {_, t2, m2}} -> m1 == m2 and subtype?(t2, t1) end) and
      r1 == r2
  end

  def subtype?(_, _), do: false

  @doc "Returns true if `a` and `b` are compatible (either is subtype of the other, or either is `:any`)."
  # Refinements only hold in the scope that introduced them. At use sites
  # that only care about whether two values can be combined (arithmetic,
  # comparisons, `if` branch joins, ...), the compatibility of the base
  # type is what matters.
  def compatible?({:refinement, a, _, _}, {:refinement, b, _, _}),
    do: compatible?(a, b)

  def compatible?({:refinement, base, _, _}, t), do: compatible?(base, t)
  def compatible?(t, {:refinement, base, _, _}), do: compatible?(t, base)
  def compatible?(a, b), do: subtype?(a, b) or subtype?(b, a)

  # -- Join (least upper bound) ------------------------------------------------

  @doc "Compute the join (least upper bound) of two types."
  def join(t, t), do: t
  def join(:never, t), do: t
  def join(t, :never), do: t
  def join(:any, _), do: :any
  def join(_, :any), do: :any
  def join(:int, :float), do: :float
  def join(:float, :int), do: :float

  # Structural joins: widen component types rather than collapsing to `:any`.
  def join({:list, a}, {:list, b}), do: {:list, join(a, b)}

  def join({:tuple, as}, {:tuple, bs}) when length(as) == length(bs) do
    {:tuple, Enum.zip(as, bs) |> Enum.map(fn {a, b} -> join(a, b) end)}
  end

  def join({:map, ka, va}, {:map, kb, vb}),
    do: {:map, join(ka, kb), join(va, vb)}

  # `Tuple` ADT is the top of the tuple lattice.
  def join({:tuple, _}, {:adt, :tuple, _} = top), do: top
  def join({:adt, :tuple, _} = top, {:tuple, _}), do: top

  # Type variables collapse to whichever concrete type is on the other side.
  def join({:type_var, _}, t), do: t
  def join(t, {:type_var, _}), do: t

  def join({:named, n}, {:named, n}), do: {:named, n}

  def join({:adt, n, ps1}, {:adt, n, ps2}) when length(ps1) == length(ps2) do
    {:adt, n, Enum.zip(ps1, ps2) |> Enum.map(fn {a, b} -> join(a, b) end)}
  end

  # Two branches that produce the same refined base collapse to the base:
  # the refinement is only sound inside the branch that introduced it.
  def join({:refinement, a, _, _}, {:refinement, b, _, _}), do: join(a, b)
  def join({:refinement, base, _, _}, t), do: join(base, t)
  def join(t, {:refinement, base, _, _}), do: join(t, base)

  def join(_, _), do: :any

  # -- Type-Expression AST Resolution ------------------------------------------

  @doc """
  Resolve a parser type-expression AST node into a canonical type.

  The parser produces type expressions as MetaAST nodes:
  - `{:variable, _, \"Int\"}` -> `:int`
  - `{:function_call, [name: \"List\"], [t]}` -> `{:list, resolve(t)}`
  - `{:function_call, [name: \"Function\", function_type: true], [a, b]}` -> `{:fun, [resolve(a)], resolve(b)}`
  """
  def resolve(nil), do: :any

  def resolve({:variable, _, "_"}), do: {:type_hole, :infer}

  def resolve({:variable, _, name}) when is_binary(name) do
    resolve_name(name)
  end

  def resolve({:function_call, meta, params}) do
    name = Keyword.get(meta, :name, "")
    is_fn_type = Keyword.get(meta, :function_type, false)

    cond do
      is_fn_type ->
        resolved = Enum.map(params, &resolve/1)
        {param_types, [ret_type]} = Enum.split(resolved, -1)
        {:fun, param_types, ret_type}

      name == "List" and length(params) == 1 ->
        {:list, resolve(hd(params))}

      name == "Map" and length(params) == 2 ->
        [k, v] = Enum.map(params, &resolve/1)
        {:map, k, v}

      name == "Set" and length(params) == 1 ->
        {:list, resolve(hd(params))}

      name in ["Sigma", "DPair"] ->
        case Cure.Types.Sigma.from_function_call(meta, params) do
          :not_sigma ->
            resolved_params = Enum.map(params, &resolve/1)
            {:adt, String.to_atom(String.downcase(name)), resolved_params}

          sigma ->
            sigma
        end

      name == "Eq" and length(params) == 3 ->
        # Propositional equality: Eq(T, a, b)
        [t_ast, a_ast, b_ast] = params
        {:eq, resolve(t_ast), a_ast, b_ast}

      name == "Pi" and length(params) >= 2 ->
        # Pi(name: T, ret_ast) -- explicit dependent function notation
        [{:param, pmeta, pname} | rest] = params

        case rest do
          [ret_ast] ->
            t_ast = Keyword.get(pmeta, :type)
            {:pi, [{pname, resolve(t_ast), :explicit}], ret_ast}

          _ ->
            resolved_params = Enum.map(params, &resolve/1)
            {:adt, String.to_atom(String.downcase(name)), resolved_params}
        end

      true ->
        # Generic parameterized type (ADT etc.)
        resolved_params = Enum.map(params, &resolve/1)
        {:adt, String.to_atom(String.downcase(name)), resolved_params}
    end
  end

  def resolve({:tuple, _, elems}) do
    {:tuple, Enum.map(elems, &resolve/1)}
  end

  # Pre-resolved type wrapped by Cure.Types.Pi to keep Reduce opaque.
  def resolve({:type_value, _meta, t}), do: t

  def resolve({:type_annotation, meta, children}) do
    if Keyword.get(meta, :refinement) do
      case Cure.Types.Refinement.from_type_annotation(meta, children) do
        nil -> :any
        refinement -> refinement
      end
    else
      case children do
        [inner] -> resolve(inner)
        _ -> :any
      end
    end
  end

  def resolve(_), do: :any

  # -- Name Resolution ---------------------------------------------------------

  defp resolve_name("Int"), do: :int
  defp resolve_name("Float"), do: :float
  defp resolve_name("String"), do: :string
  defp resolve_name("Bool"), do: :bool
  defp resolve_name("Atom"), do: :atom
  defp resolve_name("Unit"), do: :unit
  defp resolve_name("Any"), do: :any
  defp resolve_name("Never"), do: :never
  defp resolve_name("Char"), do: :char
  defp resolve_name("Binary"), do: :string
  defp resolve_name("Pid"), do: :atom
  defp resolve_name("Ref"), do: :atom
  defp resolve_name("Nat"), do: :int
  defp resolve_name("Tuple"), do: {:adt, :tuple, []}
  # Bare `List` (without a type parameter) is the top of the list
  # lattice, mirroring how `Tuple` collapses to `{:adt, :tuple, []}`.
  # That way a signature like `fn fmap(container: List, f: A -> B)`
  # interoperates with `Std.List.map`'s `List(T)` parameter.
  defp resolve_name("List"), do: {:list, :any}
  defp resolve_name("Map"), do: {:map, :any, :any}
  # Single-letter uppercase names (T, U, V, E, K, ...) are treated as implicit
  # type parameters. Without explicit `<T>` syntax this is the convention
  # used by the Cure stdlib and user code; resolving them as `{:type_var, T}`
  # lets `subtype?/2` accept any concrete type at the call site.
  defp resolve_name(<<c>>) when c in ?A..?Z, do: {:type_var, <<c>>}
  # Unknown uppercase name -> named type reference (user-defined record, ADT, etc.)
  defp resolve_name(name = <<c, _::binary>>) when c in ?A..?Z, do: {:named, name}
  defp resolve_name(_), do: :any

  # -- Pretty Printing ---------------------------------------------------------

  @doc "Convert a type to a human-readable string."
  def display(:int), do: "Int"
  def display(:float), do: "Float"
  def display(:string), do: "String"
  def display(:bool), do: "Bool"
  def display(:atom), do: "Atom"
  def display(:unit), do: "Unit"
  def display(:any), do: "Any"
  def display(:never), do: "Never"
  def display(:char), do: "Char"
  def display(:regex), do: "Regex"
  def display({:list, t}), do: "List(#{display(t)})"
  def display({:tuple, ts}), do: "%[#{Enum.map_join(ts, ", ", &display/1)}]"
  def display({:map, k, v}), do: "Map(#{display(k)}, #{display(v)})"
  def display({:fun, ps, r}), do: "(#{Enum.map_join(ps, ", ", &display/1)}) -> #{display(r)}"

  def display({:effun, ps, r, effects}) do
    base = "(#{Enum.map_join(ps, ", ", &display/1)}) -> #{display(r)}"

    if Enum.empty?(effects) do
      base
    else
      effs = effects |> Enum.sort() |> Enum.map_join(", ", &display_effect/1)
      "#{base} ! #{effs}"
    end
  end

  def display({:adt, :tuple, []}), do: "Tuple"
  def display({:adt, name, []}), do: Atom.to_string(name) |> String.capitalize()

  def display({:adt, name, ps}),
    do: "#{Atom.to_string(name) |> String.capitalize()}(#{Enum.map_join(ps, ", ", &display/1)})"

  def display({:record, name, _}), do: Atom.to_string(name) |> String.capitalize()
  def display({:named, name}), do: name
  def display({:type_var, id}) when is_binary(id), do: id
  def display({:type_var, id}), do: "t#{id}"
  def display({:type_hole, _}), do: "_"
  def display({:refinement, base, var, _pred}), do: "{#{var}: #{display(base)} | ...}"
  def display({:sigma, _, _, _} = s), do: Cure.Types.Sigma.display(s)

  def display({:eq, t, _a, _b}), do: "Eq(#{display(t)}, _, _)"

  def display({:pi, params, _ret_ast}) do
    "(#{Enum.map_join(params, ", ", fn {n, t, m} -> "#{mode_prefix(m)}#{n}: #{display(t)}" end)}) -> _"
  end

  def display({:hole, name, _ctx}), do: "?#{name}"
  def display(other), do: inspect(other)

  defp mode_prefix(:implicit), do: "{"
  defp mode_prefix(:erased), do: "@"
  defp mode_prefix(_), do: ""

  @doc "Convert an effect atom to a display string."
  def display_effect(:io), do: "Io"
  def display_effect(:state), do: "State"
  def display_effect(:exception), do: "Exception"
  def display_effect(:spawn), do: "Spawn"
  def display_effect(:extern), do: "Extern"
  def display_effect(other), do: Atom.to_string(other) |> String.capitalize()
end
