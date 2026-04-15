defmodule Cure.Optimizer.PipeInline do
  @moduledoc """
  Pipe chain inlining optimization.

  The parser desugars `a |> f(b)` into `f(a, b)` (prepending the left
  side as the first argument). This pass is a no-op when the parser
  already performs this desugaring, but it catches nested pipe chains
  that can be further simplified and marks them for the codegen to
  avoid unnecessary intermediate allocations.

  Also performs identity elimination:
  - `x |> identity` -> `x`  (when identity is the Std.Core.identity function)
  """

  @doc "Run pipe inlining. Returns `{new_ast, inline_count}`."
  @spec run(tuple()) :: {tuple(), non_neg_integer()}
  def run(ast), do: inline(ast, 0)

  # -- Identity elimination in pipe-desugared calls --------------------------

  defp inline({:function_call, meta, [arg]} = _node, count) do
    name = Keyword.get(meta, :name, "")
    is_pipe = Keyword.get(meta, :pipe, false)

    if is_pipe and name in ["identity", "Std.Core.identity"] do
      {arg, count} = inline(arg, count)
      {arg, count + 1}
    else
      {args, count} = inline_list([arg], count)
      {{:function_call, meta, args}, count}
    end
  end

  defp inline({:function_call, meta, args}, count) do
    {args, count} = inline_list(args, count)
    {{:function_call, meta, args}, count}
  end

  # -- Structural recursion --------------------------------------------------

  defp inline({:container, meta, body}, count) do
    {body, count} = inline_list(body, count)
    {{:container, meta, body}, count}
  end

  defp inline({:function_def, meta, body}, count) do
    {body, count} = inline_list(body, count)
    {{:function_def, meta, body}, count}
  end

  defp inline({:block, meta, exprs}, count) do
    {exprs, count} = inline_list(exprs, count)
    {{:block, meta, exprs}, count}
  end

  defp inline({:binary_op, meta, [left, right]}, count) do
    {left, count} = inline(left, count)
    {right, count} = inline(right, count)
    {{:binary_op, meta, [left, right]}, count}
  end

  defp inline({:conditional, meta, [c, t, e]}, count) do
    {c, count} = inline(c, count)
    {t, count} = inline(t, count)
    {e, count} = inline(e, count)
    {{:conditional, meta, [c, t, e]}, count}
  end

  defp inline({:assignment, meta, [pattern, value]}, count) do
    {value, count} = inline(value, count)
    {{:assignment, meta, [pattern, value]}, count}
  end

  defp inline({:lambda, meta, [body]}, count) do
    {body, count} = inline(body, count)
    {{:lambda, meta, [body]}, count}
  end

  defp inline(ast, count), do: {ast, count}

  defp inline_list(list, count), do: Enum.map_reduce(list, count, &inline/2)
end
