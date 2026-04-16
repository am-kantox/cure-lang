defmodule Cure.Types.ReduceTest do
  use ExUnit.Case, async: true

  alias Cure.Types.Reduce

  defp lit(v) when is_integer(v), do: {:literal, [subtype: :integer], v}
  defp lit(v) when is_boolean(v), do: {:literal, [subtype: :boolean], v}
  defp var(n), do: {:variable, [], n}
  defp binop(op, l, r), do: {:binary_op, [operator: op], [l, r]}
  defp unop(op, x), do: {:unary_op, [operator: op], [x]}

  describe "arithmetic folding" do
    test "3 + 5 == 8" do
      assert {:literal, _, 8} = Reduce.normalize(binop(:+, lit(3), lit(5)))
    end

    test "10 - 4 == 6" do
      assert {:literal, _, 6} = Reduce.normalize(binop(:-, lit(10), lit(4)))
    end

    test "6 * 7 == 42" do
      assert {:literal, _, 42} = Reduce.normalize(binop(:*, lit(6), lit(7)))
    end

    test "20 / 4 == 5 (integer division)" do
      assert {:literal, _, 5} = Reduce.normalize(binop(:/, lit(20), lit(4)))
    end

    test "division by zero is not folded" do
      ast = binop(:/, lit(10), lit(0))
      assert ^ast = Reduce.normalize(ast)
    end

    test "nested arithmetic folds completely" do
      # (3 + 5) * 2
      ast = binop(:*, binop(:+, lit(3), lit(5)), lit(2))
      assert {:literal, _, 16} = Reduce.normalize(ast)
    end
  end

  describe "boolean folding" do
    test "true and false == false" do
      assert {:literal, _, false} = Reduce.normalize(binop(:and, lit(true), lit(false)))
    end

    test "false or true == true" do
      assert {:literal, _, true} = Reduce.normalize(binop(:or, lit(false), lit(true)))
    end

    test "not true == false" do
      assert {:literal, _, false} = Reduce.normalize(unop(:not, lit(true)))
    end

    test "negate -5 == 5" do
      assert {:literal, _, -5} = Reduce.normalize(unop(:-, lit(5)))
    end
  end

  describe "comparisons" do
    test "5 == 5 -> true" do
      assert {:literal, _, true} = Reduce.normalize(binop(:==, lit(5), lit(5)))
    end

    test "3 < 5 -> true" do
      assert {:literal, _, true} = Reduce.normalize(binop(:<, lit(3), lit(5)))
    end

    test "5 >= 5 -> true" do
      assert {:literal, _, true} = Reduce.normalize(binop(:>=, lit(5), lit(5)))
    end
  end

  describe "substitution" do
    test "free variable bound to literal is substituted then folded" do
      ast = binop(:+, var("n"), lit(1))
      result = Reduce.normalize(ast, %{"n" => lit(4)})
      assert {:literal, _, 5} = result
    end

    test "unknown variable is left untouched" do
      ast = binop(:+, var("n"), lit(1))
      result = Reduce.normalize(ast, %{})
      assert {:binary_op, _, [{:variable, _, "n"}, _]} = result
    end

    test "substitute/2 does not fold" do
      ast = binop(:+, var("n"), lit(1))
      result = Reduce.substitute(ast, %{"n" => lit(4)})
      assert {:binary_op, _, [{:literal, _, 4}, {:literal, _, 1}]} = result
    end
  end

  describe "definitional equality" do
    test "3 + 5 == 8" do
      assert Reduce.equal?(binop(:+, lit(3), lit(5)), lit(8))
    end

    test "(2 * 3) + 1 == 7" do
      ast = binop(:+, binop(:*, lit(2), lit(3)), lit(1))
      assert Reduce.equal?(ast, lit(7))
    end

    test "n + 1 != 5 without bindings" do
      refute Reduce.equal?(binop(:+, var("n"), lit(1)), lit(5))
    end

    test "n + 1 == 5 with n bound to 4" do
      assert Reduce.equal?(binop(:+, var("n"), lit(1)), lit(5), %{"n" => lit(4)})
    end
  end

  describe "tuple/list passthrough" do
    test "tuples are normalised pointwise" do
      ast = {:tuple, [], [binop(:+, lit(1), lit(2)), lit(3)]}
      assert {:tuple, _, [{:literal, _, 3}, {:literal, _, 3}]} = Reduce.normalize(ast)
    end
  end

  describe "fst/snd projection" do
    test "fst of a literal pair" do
      pair = {:tuple, [], [lit(7), lit(11)]}
      ast = {:function_call, [name: "fst"], [pair]}
      assert {:literal, _, 7} = Reduce.normalize(ast)
    end

    test "snd of a literal pair" do
      pair = {:tuple, [], [lit(7), lit(11)]}
      ast = {:function_call, [name: "snd"], [pair]}
      assert {:literal, _, 11} = Reduce.normalize(ast)
    end
  end
end
