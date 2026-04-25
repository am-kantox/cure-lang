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

  alias Cure.Optimizer.{ConstantFold, DeadCode, PipeInline, Inline, GuardSimplify, Monomorphise}

  @doc """
  Run all optimization passes on a MetaAST node.

  Returns `{:ok, optimized_ast, stats}` where stats is a map
  counting the transformations applied.

  ## Options

  * `:monomorphise` -- when `false`, skip the monomorphisation pass
    (default `true`). v0.31.0 ships monomorphisation as the first
    pass; subsequent passes (Inline, ConstantFold, ...) see specialised
    signatures and can do more.
  * `:monomorph_budget` -- soft cap on specialisations per source
    function (default `16`).
  * `:pgo` -- a `Cure.PGO` summary; when present, the inliner uses
    hot/cold classification to relax or tighten its size cap. v0.31.0
    PGO is **strictly opt-in** -- pass `Cure.PGO.empty()` (or omit
    the option) for behaviour identical to pre-v0.31.0.
  * `:module` -- atom; the module name PGO classifies against. When
    omitted, PGO classification falls back to `:default` for every
    function.
  * `:emit_events` -- whether passes emit pipeline events (default `true`).
  * `:file` -- file path for event metadata (default `"nofile"`).
  """
  @spec optimize(tuple()) :: {:ok, tuple(), map()}
  @spec optimize(tuple(), keyword()) :: {:ok, tuple(), map()}
  def optimize(ast, opts \\ []) do
    monomorph? = Keyword.get(opts, :monomorphise, true)
    monomorph_budget = Keyword.get(opts, :monomorph_budget, 16)
    emit? = Keyword.get(opts, :emit_events, true)
    file = Keyword.get(opts, :file, "nofile")
    pgo = Keyword.get(opts, :pgo)
    module = Keyword.get(opts, :module)

    monomorph_runner =
      fn a ->
        if monomorph? do
          Monomorphise.run(a, budget: monomorph_budget, emit_events: emit?, file: file)
        else
          {a, 0}
        end
      end

    inline_runner = fn a -> Inline.run(a, pgo: pgo, module: module) end

    {ast, stats} =
      {ast,
       %{
         monomorphise: 0,
         constant_fold: 0,
         dead_code: 0,
         pipe_inline: 0,
         inline: 0,
         guard_simplify: 0
       }}
      |> apply_pass(monomorph_runner, :monomorphise)
      |> apply_pass(inline_runner, :inline)
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
  def run_pass(ast, :monomorphise), do: apply_single(&Monomorphise.run/1, ast)
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
