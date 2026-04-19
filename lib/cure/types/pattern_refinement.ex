defmodule Cure.Types.PatternRefinement do
  @moduledoc """
  Structural refinement narrowing for nested patterns (v0.20.0).

  When a `match` or `let` pattern destructures a scrutinee, the
  match-arm body may safely assume two things that the previous
  `Cure.Types.Checker.bind_pattern_vars/3` did not expose:

  1. **Literal-equality witnesses.** A sub-pattern that is a literal
     (`0`, `:ok`, `"hello"`) means the matched value equals that
     literal along the arm. Binding-position variables whose
     corresponding sub-pattern is a literal learn an equality
     refinement on the enclosing scrutinee.

  2. **Disjoint-tag witnesses.** A constructor pattern (`Ok(v)`,
     `Error(e)`) or a map pattern with a literal tag (`%{kind: :ok,
     value: v}`) narrows the scrutinee type to the tagged variant.

  ## Public API

    * `narrow/2` -- `(pattern_ast, scrutinee_type)` returns
      `{bindings, narrowed_scrutinee}`. `bindings` is a map from
      variable name to its narrowed type; `narrowed_scrutinee` is
      the scrutinee type with any disjoint-tag or literal-equality
      information applied.

  `Cure.Types.Checker.bind_pattern_vars/3` delegates to this module;
  callers that want the narrowed scrutinee separately (for
  path-sensitive refinement) can call `narrow/2` directly.

  ## Representation

  Narrowed types reuse the existing representations:

    * An equality witness on a base type is `{:refinement, base,
      \"__value__\", pred}` where `pred` is a MetaAST equality
      predicate over the reserved variable `__value__`.
    * A disjoint-tag witness on a sum type is `{:variant, tag_atom,
      arg_types}` -- a placeholder the SMT translator can interpret
      as the corresponding variant's shape.
  """

  alias Cure.Types.Refinement

  @typep bindings :: %{optional(String.t()) => term()}

  @doc """
  Narrow `pattern` against `scrutinee_type`. Returns
  `{bindings, narrowed_scrutinee}`.
  """
  @spec narrow(tuple() | nil, term()) :: {bindings(), term()}
  def narrow(nil, scrutinee_type), do: {%{}, scrutinee_type}

  # Wildcard -- no bindings, no narrowing.
  def narrow({:variable, _, "_"}, scrutinee_type), do: {%{}, scrutinee_type}
  def narrow({:variable, _, "_" <> _}, scrutinee_type), do: {%{}, scrutinee_type}

  # Bare variable -- bind to scrutinee type unchanged.
  def narrow({:variable, _, name}, scrutinee_type) when is_binary(name) do
    {%{name => scrutinee_type}, scrutinee_type}
  end

  # Pin operator -- no new bindings.
  def narrow({:pin, _, _}, scrutinee_type), do: {%{}, scrutinee_type}

  # Literal pattern -- narrow scrutinee to the equality refinement.
  # v0.21.0: binary literals `<<seg1, seg2, ...>>` are emitted by the
  # parser as `{:literal, [subtype: :bytes, ...], segments}` and handled
  # in a dedicated branch below. All other literal patterns fall through
  # to the scalar equality-refinement path.
  def narrow({:literal, meta, segments}, scrutinee_type)
      when is_list(segments) and length(segments) > 0 do
    case Keyword.get(meta, :subtype) do
      :bytes ->
        narrow_binary_segments(segments, scrutinee_type)

      _ ->
        narrow_scalar_literal(meta, segments, scrutinee_type)
    end
  end

  def narrow({:literal, meta, []}, scrutinee_type) do
    case Keyword.get(meta, :subtype) do
      :bytes ->
        # The empty binary `<<>>` narrows the scrutinee to a Bitstring
        # of byte size 0. We keep the representation coarse (just
        # `:bitstring`) until the checker's SMT translator learns to
        # consume a `byte_size == 0` refinement.
        {%{}, :bitstring}

      _ ->
        narrow_scalar_literal(meta, [], scrutinee_type)
    end
  end

  def narrow({:literal, meta, value}, scrutinee_type) do
    narrow_scalar_literal(meta, value, scrutinee_type)
  end

  # Unary-op (only negative integer literals in pattern position).
  def narrow({:unary_op, _meta, [inner]}, scrutinee_type) do
    narrow(inner, scrutinee_type)
  end

  # Tuple pattern.
  def narrow({:tuple, _meta, elems}, {:tuple, elem_types})
      when is_list(elem_types) and length(elems) == length(elem_types) do
    {bindings, new_types} =
      elems
      |> Enum.zip(elem_types)
      |> Enum.reduce({%{}, []}, fn {elem, t}, {acc, acc_types} ->
        {b, new_t} = narrow(elem, t)
        {Map.merge(acc, b), acc_types ++ [new_t]}
      end)

    {bindings, {:tuple, new_types}}
  end

  def narrow({:tuple, _meta, elems}, _scrutinee) do
    {bindings, _} =
      Enum.reduce(elems, {%{}, nil}, fn elem, {acc, _} ->
        {b, _} = narrow(elem, :any)
        {Map.merge(acc, b), nil}
      end)

    {bindings, :any}
  end

  # List / cons pattern.
  def narrow({:list, meta, elems}, scrutinee_type) do
    elem_type = list_elem_type(scrutinee_type)

    if Keyword.get(meta, :cons, false) do
      case elems do
        [head, tail] ->
          {head_b, _} = narrow(head, elem_type)
          {tail_b, _} = narrow(tail, scrutinee_type)
          {Map.merge(head_b, tail_b), scrutinee_type}

        _ ->
          narrow_list_elems(elems, elem_type, scrutinee_type)
      end
    else
      narrow_list_elems(elems, elem_type, scrutinee_type)
    end
  end

  # Map pattern.
  def narrow({:map, _meta, pairs}, scrutinee_type) do
    tag_witness =
      Enum.find_value(pairs, fn
        {:pair, _, [{:literal, [subtype: :symbol], :kind}, {:literal, _, tag}]}
        when is_atom(tag) ->
          tag

        {:pair, _, [{:literal, _, "kind"}, {:literal, _, tag}]}
        when is_atom(tag) ->
          tag

        _ ->
          nil
      end)

    bindings =
      Enum.reduce(pairs, %{}, fn
        {:pair, _, [_key, {:variable, _, name}]}, acc when is_binary(name) ->
          Map.put(acc, name, :any)

        {:pair, _, [_key, value_pat]}, acc ->
          {sub, _} = narrow(value_pat, :any)
          Map.merge(acc, sub)

        _, acc ->
          acc
      end)

    narrowed =
      case tag_witness do
        nil -> scrutinee_type
        tag -> {:variant, tag, []}
      end

    {bindings, narrowed}
  end

  # Record / ADT constructor / function-call-shaped pattern.
  def narrow({:function_call, meta, args} = pat, scrutinee_type) do
    cond do
      Keyword.get(meta, :record, false) ->
        narrow_record(meta, args, scrutinee_type)

      constructor?(Keyword.get(meta, :name)) ->
        narrow_constructor(meta, args, scrutinee_type)

      true ->
        {%{}, scrutinee_type}
        |> then(fn _ ->
          {_, _} = {pat, scrutinee_type}
          {%{}, scrutinee_type}
        end)
    end
  end

  def narrow(_, scrutinee_type), do: {%{}, scrutinee_type}

  # -- Helpers ----------------------------------------------------------------

  defp narrow_list_elems(elems, elem_type, scrutinee_type) do
    bindings =
      Enum.reduce(elems, %{}, fn elem, acc ->
        {b, _} = narrow(elem, elem_type)
        Map.merge(acc, b)
      end)

    {bindings, scrutinee_type}
  end

  defp narrow_record(_meta, args, scrutinee_type) do
    bindings =
      Enum.reduce(args, %{}, fn
        {:variable, _, name}, acc when is_binary(name) and name != "_" ->
          Map.put(acc, name, :any)

        {:pair, _, [_key, {:variable, _, name}]}, acc when is_binary(name) ->
          Map.put(acc, name, :any)

        {:pair, _, [_key, value_pat]}, acc ->
          {sub, _} = narrow(value_pat, :any)
          Map.merge(acc, sub)

        _, acc ->
          acc
      end)

    {bindings, scrutinee_type}
  end

  defp narrow_constructor(meta, args, scrutinee_type) do
    tag =
      case Keyword.get(meta, :name) do
        name when is_binary(name) -> String.to_atom(Macro.underscore(name))
        _ -> nil
      end

    bindings =
      Enum.reduce(args, %{}, fn arg, acc ->
        {sub, _} = narrow(arg, :any)
        Map.merge(acc, sub)
      end)

    narrowed =
      case tag do
        nil -> scrutinee_type
        _ -> {:variant, tag, []}
      end

    {bindings, narrowed}
  end

  defp constructor?(name) when is_binary(name) do
    case String.first(name) do
      nil -> false
      first -> first == String.upcase(first) and first != String.downcase(first)
    end
  end

  defp constructor?(_), do: false

  defp literal_base_type(meta) do
    case Keyword.get(meta, :subtype) do
      :integer -> :int
      :float -> :float
      :string -> :string
      :boolean -> :bool
      :symbol -> :atom
      :char -> :char
      _ -> nil
    end
  end

  defp base_of(type) when is_atom(type), do: type
  defp base_of({:refinement, base, _, _}), do: base
  defp base_of(_), do: nil

  defp list_elem_type({:list, t}), do: t
  defp list_elem_type(_), do: :any

  # v0.21.0: scalar-literal narrowing. Kept as a helper so the
  # binary-literal branch in `narrow/2` can short-circuit before we
  # reach the equality-refinement path.
  defp narrow_scalar_literal(meta, value, scrutinee_type) do
    base = literal_base_type(meta) || base_of(scrutinee_type)

    case base do
      nil ->
        {%{}, scrutinee_type}

      atom when is_atom(atom) ->
        pred = equality_predicate(value, meta)
        refined = Refinement.new(atom, "__value__", pred)
        {%{}, refined}
    end
  end

  # Walk a sequence of `{:bin_segment, meta, [value]}` children and
  # collect their variable bindings. Narrowing of `rest::binary` tail
  # segments against the preceding `::size(n)` specifiers is done in a
  # conservative form: `rest` binds to plain `:bitstring`, but future
  # releases can extend this to emit a `byte_size(rest) == byte_size(s) - n`
  # refinement once the SMT translator grows the arithmetic support.
  defp narrow_binary_segments(segments, scrutinee_type) do
    bindings =
      Enum.reduce(segments, %{}, fn seg, acc ->
        case seg do
          {:bin_segment, seg_meta, [inner]} ->
            type = bin_segment_type(seg_meta)

            case inner do
              {:variable, _, name} when is_binary(name) and name != "_" ->
                Map.put(acc, name, type)

              other ->
                {sub, _} = narrow(other, type)
                Map.merge(acc, sub)
            end

          _ ->
            acc
        end
      end)

    {bindings, scrutinee_type}
  end

  defp bin_segment_type(meta) do
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

  # Build an equality predicate `__value__ == literal`. The reserved
  # name mirrors what `Cure.Types.Refinement` uses as a placeholder
  # for the anonymous scrutinee.
  defp equality_predicate(value, lit_meta) do
    line = Keyword.get(lit_meta, :line, 1)
    op_meta = [operator: :==, category: :comparison, line: line]
    lit = {:literal, lit_meta, value}
    var = {:variable, [line: line], "__value__"}
    {:binary_op, op_meta, [var, lit]}
  end
end
