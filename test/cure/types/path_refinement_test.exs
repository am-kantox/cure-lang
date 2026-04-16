defmodule Cure.Types.PathRefinementTest do
  use ExUnit.Case, async: true

  alias Cure.Types.PathRefinement

  defp lit(v), do: {:literal, [subtype: :integer], v}
  defp var(n), do: {:variable, [], n}
  defp binop(op, l, r), do: {:binary_op, [operator: op], [l, r]}

  describe "refine_along/3 in the true branch" do
    test "x > 0 refines x" do
      cond_ast = binop(:>, var("x"), lit(0))
      result = PathRefinement.refine_along(cond_ast, :true_branch, %{"x" => :int})
      assert {:refinement, :int, "x", _} = Map.get(result, "x")
    end

    test "literal-on-the-left flips the operator" do
      cond_ast = binop(:<, lit(0), var("x"))
      # 0 < x  in true branch  is equivalent to  x > 0
      result = PathRefinement.refine_along(cond_ast, :true_branch, %{"x" => :int})
      assert Map.has_key?(result, "x")
    end

    test "is_int(x) refines x to :int" do
      cond_ast = {:function_call, [name: "is_int"], [var("x")]}
      result = PathRefinement.refine_along(cond_ast, :true_branch, %{})
      assert :int = Map.get(result, "x")
    end
  end

  describe "refine_along/3 in the false branch" do
    test "negates ==" do
      cond_ast = binop(:==, var("x"), lit(0))
      result = PathRefinement.refine_along(cond_ast, :false_branch, %{"x" => :int})
      assert {:refinement, :int, "x", _} = Map.get(result, "x")
    end
  end

  describe "negate/1" do
    test "double negation cancels" do
      ast = {:unary_op, [operator: :not], [binop(:>, var("x"), lit(0))]}
      result = PathRefinement.negate(ast)
      assert binop(:>, var("x"), lit(0)) == result
    end

    test "swaps comparison operators" do
      assert {:binary_op, meta, _} = PathRefinement.negate(binop(:<, var("x"), lit(0)))
      assert :>= = Keyword.get(meta, :operator)
    end
  end
end
