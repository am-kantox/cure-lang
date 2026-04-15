defmodule Cure.Optimizer.Inline do
  @moduledoc """
  Function inlining optimization pass.

  Identifies small, pure functions and inlines their bodies at call sites.
  This eliminates function call overhead for trivial functions.

  ## Criteria for inlining

  A function is inlinable if:
  - Its body is a single expression (not a block)
  - It is not recursive (does not call itself)
  - Its body contains no side effects (no I/O, no throw, no spawn)

  ## Example

      fn double(x: Int) -> Int = x * 2
      fn use() -> Int = double(21)

  After inlining:

      fn use() -> Int = 21 * 2

  Which constant folding then reduces to `42`.
  """

  @doc "Run function inlining. Returns `{new_ast, inline_count}`."
  @spec run(tuple()) :: {tuple(), non_neg_integer()}
  def run(ast) do
    # Phase 1: collect inlinable function bodies
    inlinables = collect_inlinables(ast)

    # Phase 2: substitute call sites
    if map_size(inlinables) > 0 do
      do_inline(ast, inlinables, 0)
    else
      {ast, 0}
    end
  end

  # -- Phase 1: collect inlinable functions ------------------------------------

  defp collect_inlinables({:container, _meta, body}) do
    Enum.reduce(body, %{}, fn
      {:function_def, meta, [body_expr]} = _fn_def, acc ->
        name = Keyword.get(meta, :name, "")
        params = Keyword.get(meta, :params, [])
        arity = length(params)

        if inlinable?(name, body_expr) do
          param_names = Enum.map(params, fn {:param, _, pname} -> pname end)
          Map.put(acc, {name, arity}, %{body: body_expr, params: param_names})
        else
          acc
        end

      _, acc ->
        acc
    end)
  end

  defp collect_inlinables({:block, _, children}) do
    Enum.reduce(children, %{}, fn child, acc ->
      Map.merge(acc, collect_inlinables(child))
    end)
  end

  defp collect_inlinables(_), do: %{}

  defp inlinable?(name, body_expr) do
    name != "" and
      not recursive?(name, body_expr) and
      not has_side_effects?(body_expr) and
      ast_size(body_expr) <= 5
  end

  defp recursive?(name, {:function_call, meta, _args}) do
    Keyword.get(meta, :name, "") == name
  end

  defp recursive?(name, {:binary_op, _, [left, right]}) do
    recursive?(name, left) or recursive?(name, right)
  end

  defp recursive?(name, {:unary_op, _, [operand]}) do
    recursive?(name, operand)
  end

  defp recursive?(_name, _), do: false

  defp has_side_effects?({:function_call, meta, args}) do
    name = Keyword.get(meta, :name, "")

    # Check explicit list of known effectful names
    known_effectful = name in ["print", "println", "put_chars", "throw", "spawn", "send", "print_int", "print_float"]

    known_effectful or Enum.any?(args, &has_side_effects?/1)
  end

  defp has_side_effects?({:early_return, _, _}), do: true
  defp has_side_effects?({:throw, _, _}), do: true
  defp has_side_effects?({:async_operation, _, _}), do: true

  defp has_side_effects?({:binary_op, _, [left, right]}) do
    has_side_effects?(left) or has_side_effects?(right)
  end

  defp has_side_effects?({:conditional, _, [c, t, e]}) do
    has_side_effects?(c) or has_side_effects?(t) or has_side_effects?(e)
  end

  defp has_side_effects?({:assignment, _, [_, val]}), do: has_side_effects?(val)

  defp has_side_effects?(_), do: false

  defp ast_size({:binary_op, _, [left, right]}), do: 1 + ast_size(left) + ast_size(right)
  defp ast_size({:unary_op, _, [operand]}), do: 1 + ast_size(operand)
  defp ast_size({:function_call, _, args}), do: 1 + Enum.sum(Enum.map(args, &ast_size/1))
  defp ast_size({:conditional, _, [c, t, e]}), do: 1 + ast_size(c) + ast_size(t) + ast_size(e)
  defp ast_size(_), do: 1

  # -- Phase 2: substitute call sites -----------------------------------------

  defp do_inline({:function_call, meta, args}, inlinables, count) do
    name = Keyword.get(meta, :name, "")
    arity = length(args)

    {inlined_args, count} =
      Enum.map_reduce(args, count, fn arg, c -> do_inline(arg, inlinables, c) end)

    case Map.get(inlinables, {name, arity}) do
      %{body: body, params: param_names} ->
        # Build substitution map: param_name -> arg_ast
        bindings =
          Enum.zip(param_names, inlined_args)
          |> Map.new()

        substituted = substitute(body, bindings)
        {substituted, count + 1}

      nil ->
        {{:function_call, meta, inlined_args}, count}
    end
  end

  defp do_inline({:container, meta, body}, inlinables, count) do
    {body, count} = Enum.map_reduce(body, count, fn item, c -> do_inline(item, inlinables, c) end)
    {{:container, meta, body}, count}
  end

  defp do_inline({:function_def, meta, body}, inlinables, count) do
    {body, count} = Enum.map_reduce(body, count, fn item, c -> do_inline(item, inlinables, c) end)
    {{:function_def, meta, body}, count}
  end

  defp do_inline({:block, meta, exprs}, inlinables, count) do
    {exprs, count} = Enum.map_reduce(exprs, count, fn e, c -> do_inline(e, inlinables, c) end)
    {{:block, meta, exprs}, count}
  end

  defp do_inline({:binary_op, meta, [left, right]}, inlinables, count) do
    {left, count} = do_inline(left, inlinables, count)
    {right, count} = do_inline(right, inlinables, count)
    {{:binary_op, meta, [left, right]}, count}
  end

  defp do_inline({:conditional, meta, [c, t, e]}, inlinables, count) do
    {c, count} = do_inline(c, inlinables, count)
    {t, count} = do_inline(t, inlinables, count)
    {e, count} = do_inline(e, inlinables, count)
    {{:conditional, meta, [c, t, e]}, count}
  end

  defp do_inline({:assignment, meta, [pat, val]}, inlinables, count) do
    {val, count} = do_inline(val, inlinables, count)
    {{:assignment, meta, [pat, val]}, count}
  end

  defp do_inline({:lambda, meta, [body]}, inlinables, count) do
    {body, count} = do_inline(body, inlinables, count)
    {{:lambda, meta, [body]}, count}
  end

  defp do_inline(ast, _inlinables, count), do: {ast, count}

  # -- Substitution ------------------------------------------------------------

  defp substitute({:variable, _meta, name} = ast, bindings) do
    Map.get(bindings, name, ast)
  end

  defp substitute({:binary_op, meta, [left, right]}, bindings) do
    {:binary_op, meta, [substitute(left, bindings), substitute(right, bindings)]}
  end

  defp substitute({:unary_op, meta, [operand]}, bindings) do
    {:unary_op, meta, [substitute(operand, bindings)]}
  end

  defp substitute({:function_call, meta, args}, bindings) do
    {:function_call, meta, Enum.map(args, &substitute(&1, bindings))}
  end

  defp substitute({:conditional, meta, [c, t, e]}, bindings) do
    {:conditional, meta, [substitute(c, bindings), substitute(t, bindings), substitute(e, bindings)]}
  end

  defp substitute(ast, _bindings), do: ast
end
