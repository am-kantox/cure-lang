defmodule Cure.Optimizer.ConstantFold do
  @moduledoc """
  Constant folding optimization pass.

  Evaluates expressions that consist entirely of literals at compile time,
  replacing them with their computed values.

  ## Examples

      2 + 3        -> 5
      10 > 5       -> true
      not false    -> true
      true and false -> false
  """

  @doc "Run constant folding on an AST. Returns `{new_ast, fold_count}`."
  @spec run(tuple()) :: {tuple(), non_neg_integer()}
  def run(ast) do
    {new_ast, count} = fold(ast, 0)
    {new_ast, count}
  end

  # -- Arithmetic binary ops on two integer literals -------------------------

  defp fold({:binary_op, meta, [left, right]} = _node, count) do
    {left, count} = fold(left, count)
    {right, count} = fold(right, count)
    op = Keyword.get(meta, :operator)
    line = Keyword.get(meta, :line, 1)

    with {a_type, a_val} <- literal_value(left),
         {b_type, b_val} <- literal_value(right) do
      cond do
        op in [:+, :-, :*, :/, :%] and a_type == :integer and b_type == :integer ->
          case eval_arith(op, a_val, b_val) do
            nil -> {{:binary_op, meta, [left, right]}, count}
            result -> {{:literal, [subtype: :integer, line: line], result}, count + 1}
          end

        op in [:==, :!=, :<, :>, :<=, :>=] and a_type == :integer and b_type == :integer ->
          result = eval_cmp(op, a_val, b_val)
          {{:literal, [subtype: :boolean, line: line], result}, count + 1}

        op in [:and, :or] and a_type == :boolean and b_type == :boolean ->
          result = eval_bool(op, a_val, b_val)
          {{:literal, [subtype: :boolean, line: line], result}, count + 1}

        op == :<> and a_type == :string and b_type == :string and is_binary(a_val) and is_binary(b_val) ->
          {{:literal, [subtype: :string, line: line], a_val <> b_val}, count + 1}

        true ->
          {{:binary_op, meta, [left, right]}, count}
      end
    else
      _ -> {{:binary_op, meta, [left, right]}, count}
    end
  end

  # -- Unary ops on literals -------------------------------------------------

  defp fold({:unary_op, meta, [operand]} = _node, count) do
    {operand, count} = fold(operand, count)
    op = Keyword.get(meta, :operator)
    line = Keyword.get(meta, :line, 1)

    case {op, literal_value(operand)} do
      {:-, {:integer, n}} ->
        {{:literal, [subtype: :integer, line: line], -n}, count + 1}

      {:not, {:boolean, b}} ->
        {{:literal, [subtype: :boolean, line: line], !b}, count + 1}

      _ ->
        {{:unary_op, meta, [operand]}, count}
    end
  end

  # -- Structural recursion for containers -----------------------------------

  defp fold({:container, meta, body}, count) do
    {body, count} = fold_list(body, count)
    {{:container, meta, body}, count}
  end

  defp fold({:function_def, meta, body}, count) do
    {body, count} = fold_list(body, count)
    {{:function_def, meta, body}, count}
  end

  defp fold({:block, meta, exprs}, count) do
    {exprs, count} = fold_list(exprs, count)
    {{:block, meta, exprs}, count}
  end

  defp fold({:conditional, meta, [cond_ast, then_ast, else_ast]}, count) do
    {cond_ast, count} = fold(cond_ast, count)
    {then_ast, count} = fold(then_ast, count)
    {else_ast, count} = fold(else_ast, count)
    {{:conditional, meta, [cond_ast, then_ast, else_ast]}, count}
  end

  defp fold({:assignment, meta, [pattern, value]}, count) do
    {value, count} = fold(value, count)
    {{:assignment, meta, [pattern, value]}, count}
  end

  defp fold({:function_call, meta, args}, count) do
    {args, count} = fold_list(args, count)
    {{:function_call, meta, args}, count}
  end

  defp fold({:list, meta, elems}, count) do
    {elems, count} = fold_list(elems, count)
    {{:list, meta, elems}, count}
  end

  defp fold({:pattern_match, meta, [scrutinee | arms]}, count) do
    {scrutinee, count} = fold(scrutinee, count)
    {{:pattern_match, meta, [scrutinee | arms]}, count}
  end

  defp fold({:lambda, meta, [body]}, count) do
    {body, count} = fold(body, count)
    {{:lambda, meta, [body]}, count}
  end

  # Leaves (literals, variables, etc.) -- no folding
  defp fold(ast, count), do: {ast, count}

  # Extract literal type and value from a literal AST node
  defp literal_value({:literal, meta, value}) do
    case Keyword.get(meta, :subtype) do
      nil -> nil
      subtype -> {subtype, value}
    end
  end

  defp literal_value(_), do: nil

  defp fold_list(list, count) do
    Enum.map_reduce(list, count, &fold/2)
  end

  # -- Evaluation helpers ----------------------------------------------------

  defp eval_arith(:+, a, b), do: a + b
  defp eval_arith(:-, a, b), do: a - b
  defp eval_arith(:*, a, b), do: a * b
  defp eval_arith(:/, _a, 0), do: nil
  defp eval_arith(:/, a, b), do: div(a, b)
  defp eval_arith(:%, _a, 0), do: nil
  defp eval_arith(:%, a, b), do: rem(a, b)

  defp eval_cmp(:==, a, b), do: a == b
  defp eval_cmp(:!=, a, b), do: a != b
  defp eval_cmp(:<, a, b), do: a < b
  defp eval_cmp(:>, a, b), do: a > b
  defp eval_cmp(:<=, a, b), do: a <= b
  defp eval_cmp(:>=, a, b), do: a >= b

  defp eval_bool(:and, a, b), do: a and b
  defp eval_bool(:or, a, b), do: a or b
end
