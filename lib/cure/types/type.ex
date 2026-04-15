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
  - `{:record, name_atom, %{field_atom => type}}`
  - `{:type_var, id}` -- fresh unification variable (future use)
  - `{:refinement, base_type, var_name, predicate_ast}` -- structural only
  - `{:effun, [param_types], return_type, effects}` -- effectful function type

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
  def subtype?(_, {:type_hole, _}), do: true
  def subtype?({:type_hole, _}, _), do: true
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

  def subtype?(_, _), do: false

  @doc "Returns true if `a` and `b` are compatible (either is subtype of the other, or either is `:any`)."
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

      true ->
        # Generic parameterized type (ADT etc.)
        resolved_params = Enum.map(params, &resolve/1)
        {:adt, String.to_atom(String.downcase(name)), resolved_params}
    end
  end

  def resolve({:tuple, _, elems}) do
    {:tuple, Enum.map(elems, &resolve/1)}
  end

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
  # Single-letter uppercase -> type variable (future); treat as :any for Phase 1
  defp resolve_name(<<c, _::binary>>) when c in ?A..?Z, do: :any
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

  def display({:adt, name, []}), do: Atom.to_string(name) |> String.capitalize()

  def display({:adt, name, ps}),
    do: "#{Atom.to_string(name) |> String.capitalize()}(#{Enum.map_join(ps, ", ", &display/1)})"

  def display({:record, name, _}), do: Atom.to_string(name) |> String.capitalize()
  def display({:type_var, id}), do: "t#{id}"
  def display({:type_hole, _}), do: "_"
  def display({:refinement, base, var, _pred}), do: "{#{var}: #{display(base)} | ...}"
  def display(other), do: inspect(other)

  @doc "Convert an effect atom to a display string."
  def display_effect(:io), do: "Io"
  def display_effect(:state), do: "State"
  def display_effect(:exception), do: "Exception"
  def display_effect(:spawn), do: "Spawn"
  def display_effect(:extern), do: "Extern"
  def display_effect(other), do: Atom.to_string(other) |> String.capitalize()
end
