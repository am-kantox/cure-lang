defmodule Cure.Optimizer.GuardSimplify do
  @moduledoc """
  Guard expression simplification pass.

  Applies algebraic rules to simplify guard expressions:

  - `x > 0 and x > 0` -> `x > 0` (duplicate elimination)
  - `true and P` -> `P` (identity)
  - `false and P` -> `false` (short-circuit)
  - `true or P` -> `true` (short-circuit)
  - `false or P` -> `P` (identity)
  - `not not P` -> `P` (double negation)
  - `not true` -> `false`
  - `not false` -> `true`
  """

  @doc "Run guard simplification. Returns `{new_ast, simplification_count}`."
  @spec run(tuple()) :: {tuple(), non_neg_integer()}
  def run(ast), do: simplify(ast, 0)

  # -- Boolean simplification --------------------------------------------------

  # and: duplicate elimination
  defp simplify({:binary_op, meta, [left, right]} = _node, count) do
    {left, count} = simplify(left, count)
    {right, count} = simplify(right, count)
    op = Keyword.get(meta, :operator)

    case op do
      :and ->
        cond do
          # P and P -> P
          left == right ->
            {left, count + 1}

          # true and P -> P
          literal_bool?(left, true) ->
            {right, count + 1}

          # P and true -> P
          literal_bool?(right, true) ->
            {left, count + 1}

          # false and P -> false
          literal_bool?(left, false) ->
            {left, count + 1}

          # P and false -> false
          literal_bool?(right, false) ->
            {right, count + 1}

          true ->
            {{:binary_op, meta, [left, right]}, count}
        end

      :or ->
        cond do
          # P or P -> P
          left == right ->
            {left, count + 1}

          # true or P -> true
          literal_bool?(left, true) ->
            {left, count + 1}

          # false or P -> P
          literal_bool?(left, false) ->
            {right, count + 1}

          # P or true -> true
          literal_bool?(right, true) ->
            {right, count + 1}

          # P or false -> P
          literal_bool?(right, false) ->
            {left, count + 1}

          true ->
            {{:binary_op, meta, [left, right]}, count}
        end

      _ ->
        {{:binary_op, meta, [left, right]}, count}
    end
  end

  # not: double negation, constant folding
  defp simplify({:unary_op, meta, [operand]}, count) do
    {operand, count} = simplify(operand, count)
    op = Keyword.get(meta, :operator)

    case op do
      :not ->
        cond do
          # not (not P) -> P
          match?({:unary_op, [{:operator, :not} | _], _}, operand) ->
            {:unary_op, _, [inner]} = operand
            {inner, count + 1}

          # not true -> false
          literal_bool?(operand, true) ->
            {{:literal, [subtype: :boolean], false}, count + 1}

          # not false -> true
          literal_bool?(operand, false) ->
            {{:literal, [subtype: :boolean], true}, count + 1}

          true ->
            {{:unary_op, meta, [operand]}, count}
        end

      _ ->
        {{:unary_op, meta, [operand]}, count}
    end
  end

  # Structural recursion
  defp simplify({:container, meta, body}, count) do
    {body, count} = Enum.map_reduce(body, count, &simplify/2)
    {{:container, meta, body}, count}
  end

  defp simplify({:function_def, meta, body}, count) do
    {body, count} = Enum.map_reduce(body, count, &simplify/2)
    {{:function_def, meta, body}, count}
  end

  defp simplify({:block, meta, exprs}, count) do
    {exprs, count} = Enum.map_reduce(exprs, count, &simplify/2)
    {{:block, meta, exprs}, count}
  end

  defp simplify({:conditional, meta, [c, t, e]}, count) do
    {c, count} = simplify(c, count)
    {t, count} = simplify(t, count)
    {e, count} = simplify(e, count)
    {{:conditional, meta, [c, t, e]}, count}
  end

  defp simplify(ast, count), do: {ast, count}

  # -- Helpers -----------------------------------------------------------------

  defp literal_bool?({:literal, meta, value}, expected) do
    Keyword.get(meta, :subtype) == :boolean and value == expected
  end

  defp literal_bool?(_, _), do: false
end
