defmodule Cure.OptimizerTest do
  use ExUnit.Case, async: true

  alias Cure.Optimizer
  alias Cure.Optimizer.{ConstantFold, DeadCode, PipeInline, Inline, GuardSimplify}

  # -- AST Helpers -------------------------------------------------------------

  defp int(n), do: {:literal, [subtype: :integer, line: 1], n}
  defp bool(b), do: {:literal, [subtype: :boolean, line: 1], b}
  defp str(s), do: {:literal, [subtype: :string, line: 1], s}
  defp var(name), do: {:variable, [scope: :local, line: 1], name}

  defp binop(op, left, right) do
    cat =
      cond do
        op in [:+, :-, :*, :/, :%] -> :arithmetic
        op in [:==, :!=, :<, :>, :<=, :>=] -> :comparison
        op in [:and, :or] -> :boolean
        op == :<> -> :string
        true -> :other
      end

    {:binary_op, [operator: op, category: cat, line: 1], [left, right]}
  end

  defp unop(op, operand) do
    cat = if op == :not, do: :boolean, else: :arithmetic
    {:unary_op, [operator: op, category: cat, line: 1], [operand]}
  end

  defp cond_ast(c, t, e), do: {:conditional, [line: 1], [c, t, e]}
  defp block(exprs), do: {:block, [line: 1], exprs}
  defp ret(expr), do: {:early_return, [line: 1], [expr]}
  defp throw_ast(expr), do: {:throw, [line: 1], [expr]}

  defp pipe_call(name, args) do
    {:function_call, [name: name, pipe: true, line: 1], args}
  end

  # ============================================================================
  # Constant Folding
  # ============================================================================

  describe "ConstantFold" do
    test "fold integer addition" do
      ast = binop(:+, int(2), int(3))
      {result, count} = ConstantFold.run(ast)
      assert {:literal, _, 5} = result
      assert count == 1
    end

    test "fold integer subtraction" do
      ast = binop(:-, int(10), int(3))
      {result, _} = ConstantFold.run(ast)
      assert {:literal, _, 7} = result
    end

    test "fold integer multiplication" do
      ast = binop(:*, int(4), int(5))
      {result, _} = ConstantFold.run(ast)
      assert {:literal, _, 20} = result
    end

    test "fold integer division" do
      ast = binop(:/, int(10), int(3))
      {result, _} = ConstantFold.run(ast)
      assert {:literal, _, 3} = result
    end

    test "safe division by zero: no fold" do
      ast = binop(:/, int(10), int(0))
      {result, count} = ConstantFold.run(ast)
      assert {:binary_op, _, _} = result
      assert count == 0
    end

    test "fold comparison" do
      assert {{:literal, _, true}, 1} = ConstantFold.run(binop(:>, int(5), int(3)))
      assert {{:literal, _, false}, 1} = ConstantFold.run(binop(:<, int(5), int(3)))
      assert {{:literal, _, true}, 1} = ConstantFold.run(binop(:==, int(3), int(3)))
      assert {{:literal, _, true}, 1} = ConstantFold.run(binop(:!=, int(3), int(4)))
    end

    test "fold boolean operations" do
      assert {{:literal, _, true}, 1} = ConstantFold.run(binop(:and, bool(true), bool(true)))
      assert {{:literal, _, false}, 1} = ConstantFold.run(binop(:and, bool(true), bool(false)))
      assert {{:literal, _, true}, 1} = ConstantFold.run(binop(:or, bool(false), bool(true)))
    end

    test "fold unary negation" do
      {result, 1} = ConstantFold.run(unop(:-, int(5)))
      assert {:literal, _, -5} = result
    end

    test "fold unary not" do
      {result, 1} = ConstantFold.run(unop(:not, bool(false)))
      assert {:literal, _, true} = result
    end

    test "fold nested expression: (2 + 3) * 4" do
      ast = binop(:*, binop(:+, int(2), int(3)), int(4))
      {result, count} = ConstantFold.run(ast)
      assert {:literal, _, 20} = result
      assert count == 2
    end

    test "no fold when variables present" do
      ast = binop(:+, var("x"), int(3))
      {result, count} = ConstantFold.run(ast)
      assert {:binary_op, _, _} = result
      assert count == 0
    end

    test "fold string concatenation" do
      ast = binop(:<>, str("hello"), str(" world"))
      {result, count} = ConstantFold.run(ast)
      assert {:literal, _, "hello world"} = result
      assert count == 1
    end
  end

  # ============================================================================
  # Dead Code Elimination
  # ============================================================================

  describe "DeadCode" do
    test "eliminate if true branch" do
      ast = cond_ast(bool(true), int(42), int(0))
      {result, count} = DeadCode.run(ast)
      assert {:literal, _, 42} = result
      assert count == 1
    end

    test "eliminate if false branch" do
      ast = cond_ast(bool(false), int(42), int(0))
      {result, count} = DeadCode.run(ast)
      assert {:literal, _, 0} = result
      assert count == 1
    end

    test "keep conditional with variable condition" do
      ast = cond_ast(var("x"), int(42), int(0))
      {result, count} = DeadCode.run(ast)
      assert {:conditional, _, _} = result
      assert count == 0
    end

    test "trim block after return" do
      ast = block([int(1), ret(int(2)), int(3), int(4)])
      {result, count} = DeadCode.run(ast)
      {:block, _, exprs} = result
      assert length(exprs) == 2
      assert count == 2
    end

    test "trim block after throw" do
      ast = block([throw_ast(str("error")), int(99)])
      {result, count} = DeadCode.run(ast)
      {:block, _, exprs} = result
      assert length(exprs) == 1
      assert count == 1
    end

    test "keep block without terminal" do
      ast = block([int(1), int(2), int(3)])
      {result, count} = DeadCode.run(ast)
      {:block, _, exprs} = result
      assert length(exprs) == 3
      assert count == 0
    end
  end

  # ============================================================================
  # Pipe Inlining
  # ============================================================================

  describe "PipeInline" do
    test "eliminate identity pipe" do
      # x |> identity -> x (after parser desugaring: identity(x) with pipe: true)
      ast = pipe_call("identity", [var("x")])
      {result, count} = PipeInline.run(ast)
      assert {:variable, _, "x"} = result
      assert count == 1
    end

    test "keep non-identity pipe" do
      ast = pipe_call("double", [var("x")])
      {result, count} = PipeInline.run(ast)
      assert {:function_call, _, _} = result
      assert count == 0
    end

    test "eliminate qualified identity" do
      ast = pipe_call("Std.Core.identity", [var("x")])
      {result, count} = PipeInline.run(ast)
      assert {:variable, _, "x"} = result
      assert count == 1
    end
  end

  # ============================================================================
  # Function Inlining
  # ============================================================================

  describe "Inline" do
    test "inline simple pure function" do
      # mod with: fn double(x) = x * 2; fn use() = double(21)
      double_fn =
        {:function_def, [name: "double", params: [{:param, [], "x"}], visibility: :public, arity: 1, line: 1],
         [binop(:*, var("x"), int(2))]}

      use_fn =
        {:function_def, [name: "use_it", params: [], visibility: :public, arity: 0, line: 2],
         [{:function_call, [name: "double", line: 2], [int(21)]}]}

      ast = {:container, [container_type: :module, name: "Test"], [double_fn, use_fn]}
      {result, count} = Inline.run(ast)
      assert count >= 1

      # The call to double(21) should be replaced with 21 * 2
      {:container, _, [_, {:function_def, _, [body]}]} = result
      assert {:binary_op, _, _} = body
    end

    test "do not inline recursive functions" do
      # fn fact(n) = n * fact(n - 1)  -- should NOT be inlined
      fact_fn =
        {:function_def, [name: "fact", params: [{:param, [], "n"}], visibility: :public, arity: 1, line: 1],
         [binop(:*, var("n"), {:function_call, [name: "fact", line: 1], [binop(:-, var("n"), int(1))]})]}

      call_fn =
        {:function_def, [name: "use_it", params: [], visibility: :public, arity: 0, line: 2],
         [{:function_call, [name: "fact", line: 2], [int(5)]}]}

      ast = {:container, [container_type: :module, name: "Test"], [fact_fn, call_fn]}
      {_result, count} = Inline.run(ast)
      assert count == 0
    end

    test "do not inline functions with side effects" do
      print_fn =
        {:function_def, [name: "say_hi", params: [], visibility: :public, arity: 0, line: 1],
         [{:function_call, [name: "println", line: 1], [str("hi")]}]}

      ast = {:container, [container_type: :module, name: "Test"], [print_fn]}
      {_result, count} = Inline.run(ast)
      assert count == 0
    end
  end

  # ============================================================================
  # Guard Simplification
  # ============================================================================

  describe "GuardSimplify" do
    test "P and P -> P" do
      p = binop(:>, var("x"), int(0))
      ast = binop(:and, p, p)
      {result, count} = GuardSimplify.run(ast)
      assert result == p
      assert count == 1
    end

    test "true and P -> P" do
      p = binop(:>, var("x"), int(0))
      ast = binop(:and, bool(true), p)
      {result, count} = GuardSimplify.run(ast)
      assert result == p
      assert count == 1
    end

    test "false and P -> false" do
      p = binop(:>, var("x"), int(0))
      ast = binop(:and, bool(false), p)
      {result, count} = GuardSimplify.run(ast)
      assert {:literal, _, false} = result
      assert count == 1
    end

    test "true or P -> true" do
      p = binop(:>, var("x"), int(0))
      ast = binop(:or, bool(true), p)
      {result, count} = GuardSimplify.run(ast)
      assert {:literal, _, true} = result
      assert count == 1
    end

    test "false or P -> P" do
      p = binop(:>, var("x"), int(0))
      ast = binop(:or, bool(false), p)
      {result, count} = GuardSimplify.run(ast)
      assert result == p
      assert count == 1
    end

    test "not true -> false" do
      ast = unop(:not, bool(true))
      {result, count} = GuardSimplify.run(ast)
      assert {:literal, _, false} = result
      assert count == 1
    end

    test "not false -> true" do
      ast = unop(:not, bool(false))
      {result, count} = GuardSimplify.run(ast)
      assert {:literal, _, true} = result
      assert count == 1
    end
  end

  # ============================================================================
  # Full Optimizer Pipeline
  # ============================================================================

  describe "Optimizer.optimize" do
    test "applies all passes" do
      # if (2 > 1) then 42 else 0
      # -> constant fold: 2 > 1 -> true
      # -> dead code: if true then 42 else 0 -> 42
      ast = cond_ast(binop(:>, int(2), int(1)), int(42), int(0))
      {:ok, result, stats} = Optimizer.optimize(ast)
      assert {:literal, _, 42} = result
      assert stats.constant_fold >= 1
      assert stats.dead_code >= 1
    end

    test "run_pass for individual pass" do
      ast = binop(:+, int(3), int(4))
      {:ok, result, count} = Optimizer.run_pass(ast, :constant_fold)
      assert {:literal, _, 7} = result
      assert count == 1
    end
  end

  # ============================================================================
  # End-to-end: optimized compilation
  # ============================================================================

  describe "end-to-end optimized compilation" do
    test "compile with optimize: true produces same result" do
      source = """
      mod OptTest
        fn answer() -> Int = 6 * 7
      """

      {:ok, m} = Cure.Compiler.compile_and_load(source, optimize: true)
      assert m.answer() == 42
    after
      :code.purge(:opttest)
      :code.delete(:opttest)
    end
  end
end
