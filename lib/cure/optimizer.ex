defmodule Cure.Optimizer do
  @moduledoc """
  MetaAST optimization pass manager.

  Applies transformation passes to the MetaAST between type checking
  and code generation. Each pass rewrites the AST to produce equivalent
  but more efficient code.

  ## Passes

  1. **Constant folding** -- evaluate constant expressions at compile time
  2. **Dead code elimination** -- remove unreachable branches and unused bindings
  3. **Pipe chain inlining** -- convert `a |> f |> g` to direct `g(f(a))`

  ## Usage

      {:ok, optimized_ast} = Cure.Optimizer.optimize(ast)
  """

  alias Cure.Optimizer.{ConstantFold, DeadCode, PipeInline, Inline, GuardSimplify}

  @doc """
  Run all optimization passes on a MetaAST node.

  Returns `{:ok, optimized_ast, stats}` where stats is a map
  counting the transformations applied.
  """
  @spec optimize(tuple()) :: {:ok, tuple(), map()}
  def optimize(ast) do
    {ast, stats} =
      {ast, %{constant_fold: 0, dead_code: 0, pipe_inline: 0, inline: 0, guard_simplify: 0}}
      |> apply_pass(&Inline.run/1, :inline)
      |> apply_pass(&ConstantFold.run/1, :constant_fold)
      |> apply_pass(&DeadCode.run/1, :dead_code)
      |> apply_pass(&PipeInline.run/1, :pipe_inline)
      |> apply_pass(&GuardSimplify.run/1, :guard_simplify)

    {:ok, ast, stats}
  end

  @doc """
  Run a single named optimization pass.
  """
  @spec run_pass(tuple(), atom()) :: {:ok, tuple(), integer()}
  def run_pass(ast, :constant_fold), do: apply_single(&ConstantFold.run/1, ast)
  def run_pass(ast, :dead_code), do: apply_single(&DeadCode.run/1, ast)
  def run_pass(ast, :pipe_inline), do: apply_single(&PipeInline.run/1, ast)
  def run_pass(ast, :inline), do: apply_single(&Inline.run/1, ast)
  def run_pass(ast, :guard_simplify), do: apply_single(&GuardSimplify.run/1, ast)
  def run_pass(ast, _unknown), do: {:ok, ast, 0}

  defp apply_pass({ast, stats}, pass_fn, key) do
    {new_ast, count} = pass_fn.(ast)
    {new_ast, Map.put(stats, key, count)}
  end

  defp apply_single(pass_fn, ast) do
    {new_ast, count} = pass_fn.(ast)
    {:ok, new_ast, count}
  end
end
