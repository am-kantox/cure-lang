defmodule Cure.Optimizer.DeadCode do
  @moduledoc """
  Dead code elimination pass.

  Removes unreachable branches when the condition is a compile-time constant:

  - `if true then A else B` -> `A`
  - `if false then A else B` -> `B`
  - Blocks where expressions after `return`/`throw` are unreachable
  """

  @doc "Run dead code elimination. Returns `{new_ast, elimination_count}`."
  @spec run(tuple()) :: {tuple(), non_neg_integer()}
  def run(ast), do: elim(ast, 0)

  # -- Conditional with constant condition -----------------------------------

  defp elim({:conditional, meta, [condition, then_ast, else_ast]}, count) do
    {condition, count} = elim(condition, count)
    {then_ast, count} = elim(then_ast, count)
    {else_ast, count} = elim(else_ast, count)

    case literal_bool(condition) do
      true -> {then_ast, count + 1}
      false -> {else_ast, count + 1}
      nil -> {{:conditional, meta, [condition, then_ast, else_ast]}, count}
    end
  end

  # -- Block: remove expressions after early_return or throw -----------------

  defp elim({:block, meta, exprs}, count) do
    {exprs, count} = elim_list(exprs, count)
    {kept, removed} = trim_after_terminal(exprs)
    count = count + length(removed)
    {{:block, meta, kept}, count}
  end

  # -- Structural recursion --------------------------------------------------

  defp elim({:container, meta, body}, count) do
    {body, count} = elim_list(body, count)
    {{:container, meta, body}, count}
  end

  defp elim({:function_def, meta, body}, count) do
    {body, count} = elim_list(body, count)
    {{:function_def, meta, body}, count}
  end

  defp elim({:binary_op, meta, [left, right]}, count) do
    {left, count} = elim(left, count)
    {right, count} = elim(right, count)
    {{:binary_op, meta, [left, right]}, count}
  end

  defp elim({:assignment, meta, [pattern, value]}, count) do
    {value, count} = elim(value, count)
    {{:assignment, meta, [pattern, value]}, count}
  end

  defp elim({:function_call, meta, args}, count) do
    {args, count} = elim_list(args, count)
    {{:function_call, meta, args}, count}
  end

  defp elim({:lambda, meta, [body]}, count) do
    {body, count} = elim(body, count)
    {{:lambda, meta, [body]}, count}
  end

  defp elim(ast, count), do: {ast, count}

  defp elim_list(list, count), do: Enum.map_reduce(list, count, &elim/2)

  # -- Trim after terminal expressions ---------------------------------------

  defp trim_after_terminal(exprs) do
    {kept, rest} =
      Enum.split_while(exprs, fn expr ->
        not terminal_expr?(expr)
      end)

    case rest do
      [] -> {kept, []}
      [terminal | after_terminal] -> {kept ++ [terminal], after_terminal}
    end
  end

  defp terminal_expr?({:early_return, _, _}), do: true
  defp terminal_expr?({:throw, _, _}), do: true
  defp terminal_expr?(_), do: false

  defp literal_bool({:literal, meta, value}) do
    if Keyword.get(meta, :subtype) == :boolean, do: value, else: nil
  end

  defp literal_bool(_), do: nil
end
