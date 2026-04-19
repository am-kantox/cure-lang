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
  # collect their variable bindings.
  #
  # v0.22.0: trailing `rest::binary` (or `rest::bytes`/`rest::bitstring`)
  # tail segments now receive a `byte_size` refinement that ties them to
  # the enclosing scrutinee's byte size:
  #
  #   byte_size(__value__) == byte_size(__scrutinee__) - sum_of_preceding
  #
  # where `__value__` is the tail's own length and `__scrutinee__` is a
  # symbolic reference to the full match value. `sum_of_preceding` is an
  # arithmetic sum of each preceding segment's byte count, computed from
  # the specifier's `:size`/`:unit` entries. When a preceding segment's
  # size cannot be linearised (e.g. a non-literal variable size with an
  # unusual unit), the segment is skipped and the pipeline emits a
  # warning under code `E037`; in that case the tail still binds to
  # plain `Bitstring` for backward compatibility.
  defp narrow_binary_segments(segments, scrutinee_type) do
    {bindings, _} = segments_bindings(segments, %{}, :preceding)
    {bindings, scrutinee_type}
  end

  defp segments_bindings([], acc, _phase), do: {acc, []}

  defp segments_bindings([seg], acc, _phase) do
    # The final segment may be the `rest::binary` tail.
    acc = refine_final_segment(seg, segments_preceding(), acc)
    {acc, []}
  end

  defp segments_bindings([seg | rest], acc, phase) do
    acc =
      case seg do
        {:bin_segment, seg_meta, [inner]} ->
          bind_preceding_segment(inner, seg_meta, acc)

        _ ->
          acc
      end

    # Track the segment in the preceding-size accumulator so the final
    # segment's refinement can reference it. The per-call state is
    # threaded via the process dictionary because `segments_bindings/3`
    # is purely functional and we want to keep the public surface of
    # `narrow_binary_segments/2` unchanged.
    track_preceding(seg)
    segments_bindings(rest, acc, phase)
  end

  defp bind_preceding_segment({:variable, _, name}, seg_meta, acc)
       when is_binary(name) and name != "_" do
    Map.put(acc, name, bin_segment_type(seg_meta))
  end

  defp bind_preceding_segment(other, seg_meta, acc) do
    {sub, _} = narrow(other, bin_segment_type(seg_meta))
    Map.merge(acc, sub)
  end

  # Narrowing is scoped to `narrow_binary_segments/2`, so we use the
  # process dictionary to thread the list of preceding segments without
  # changing the public arity.
  defp track_preceding(seg) do
    list = Process.get(:cure_pr_preceding, [])
    Process.put(:cure_pr_preceding, list ++ [seg])
    :ok
  end

  defp segments_preceding do
    list = Process.get(:cure_pr_preceding, [])
    Process.delete(:cure_pr_preceding)
    list
  end

  defp refine_final_segment({:bin_segment, seg_meta, [inner]} = seg, preceding, acc) do
    base_type = bin_segment_type(seg_meta)

    case inner do
      {:variable, _, name} when is_binary(name) and name != "_" ->
        narrowed = maybe_byte_size_refinement(name, seg, seg_meta, base_type, preceding)
        Map.put(acc, name, narrowed)

      other ->
        {sub, _} = narrow(other, base_type)
        Map.merge(acc, sub)
    end
  end

  defp refine_final_segment(_, _preceding, acc), do: acc

  # Decide whether the final segment is eligible for the `byte_size`
  # refinement. Only `binary`/`bytes`/`bitstring` tails without an
  # explicit size specifier qualify (that is the `rest::binary` shape).
  defp maybe_byte_size_refinement(name, _seg, seg_meta, base_type, preceding) do
    tail_kind = Keyword.get(seg_meta, :type, :integer)
    has_size? = Keyword.has_key?(seg_meta, :size)

    tail? = tail_kind in [:binary, :bytes, :bitstring, :bits] and not has_size?

    if tail? and base_type == :bitstring do
      build_byte_size_refinement(name, preceding) || base_type
    else
      base_type
    end
  end

  # Build `{:refinement, :bitstring, "__value__",
  #   byte_size(__value__) == byte_size(__scrutinee__) - sum}` when every
  # preceding segment has a resolvable byte count; otherwise `nil`.
  defp build_byte_size_refinement(_name, preceding) do
    case sum_preceding_bytes(preceding, []) do
      {:ok, sum_ast} ->
        line = 1
        eq_meta = [operator: :==, category: :comparison, line: line]
        minus_meta = [operator: :-, category: :arithmetic, line: line]

        value_bytes =
          {:function_call, [name: "byte_size", line: line], [{:variable, [line: line], "__value__"}]}

        scrut_bytes =
          {:function_call, [name: "byte_size", line: line], [{:variable, [line: line], "__scrutinee__"}]}

        rhs = {:binary_op, minus_meta, [scrut_bytes, sum_ast]}
        pred = {:binary_op, eq_meta, [value_bytes, rhs]}

        Refinement.new(:bitstring, "__value__", pred)

      :unknown ->
        emit_refinement_downgrade_warning()
        nil
    end
  end

  defp sum_preceding_bytes([], []), do: {:ok, {:literal, [subtype: :integer, line: 1], 0}}

  defp sum_preceding_bytes([], [single]), do: {:ok, single}

  defp sum_preceding_bytes([], [first | rest]) do
    line = 1
    plus_meta = [operator: :+, category: :arithmetic, line: line]

    ast =
      Enum.reduce(rest, first, fn term, acc ->
        {:binary_op, plus_meta, [acc, term]}
      end)

    {:ok, ast}
  end

  defp sum_preceding_bytes([seg | rest], acc) do
    case segment_byte_size(seg) do
      {:ok, ast} -> sum_preceding_bytes(rest, acc ++ [ast])
      :unknown -> :unknown
    end
  end

  # Map a single segment to its byte count as a MetaAST arithmetic
  # expression. Returns `:unknown` when the segment's size cannot be
  # linearised (dynamic size with unusual unit, etc.).
  defp segment_byte_size({:bin_segment, meta, _children}) do
    type = Keyword.get(meta, :type, :integer)
    size = Keyword.get(meta, :size)
    unit = Keyword.get(meta, :unit)

    default_unit =
      case type do
        t when t in [:integer, :float] -> 1
        t when t in [:utf8, :utf16, :utf32] -> 1
        t when t in [:binary, :bytes, :bitstring, :bits] -> 8
        _ -> 1
      end

    default_size =
      case type do
        :integer -> 8
        :float -> 64
        :utf8 -> 8
        :utf16 -> 16
        :utf32 -> 32
        :binary -> nil
        :bytes -> nil
        :bitstring -> nil
        :bits -> nil
        _ -> 8
      end

    size_value = resolve_size_literal(size) || default_size
    unit_value = resolve_unit_literal(unit) || default_unit

    cond do
      size_value == nil ->
        :unknown

      is_integer(size_value) and is_integer(unit_value) and
          rem(size_value * unit_value, 8) == 0 ->
        {:ok, {:literal, [subtype: :integer, line: 1], div(size_value * unit_value, 8)}}

      true ->
        :unknown
    end
  end

  defp segment_byte_size(_), do: :unknown

  defp resolve_size_literal(nil), do: nil
  defp resolve_size_literal({:literal, _, value}) when is_integer(value), do: value
  defp resolve_size_literal(_), do: nil

  defp resolve_unit_literal(nil), do: nil
  defp resolve_unit_literal(n) when is_integer(n), do: n
  defp resolve_unit_literal({:literal, _, value}) when is_integer(value), do: value
  defp resolve_unit_literal(_), do: nil

  # Pipeline warning emitted when a segment's size cannot be linearised;
  # the tail segment stays bound to plain `:bitstring` in that case.
  defp emit_refinement_downgrade_warning do
    if Code.ensure_loaded?(Cure.Pipeline.Events) do
      Cure.Pipeline.Events.emit(
        :type_checker,
        :refinement_ignored,
        {:binary_size_non_linear, "binary segment size is non-linear; rest::binary refinement downgraded (E037)"},
        %{}
      )
    end

    :ok
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
