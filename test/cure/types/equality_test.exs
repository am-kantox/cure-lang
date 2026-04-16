defmodule Cure.Types.EqualityTest do
  use ExUnit.Case, async: true

  alias Cure.Types.Equality

  defp lit(v), do: {:literal, [subtype: :integer], v}
  defp var(n), do: {:variable, [], n}
  defp binop(op, l, r), do: {:binary_op, [operator: op], [l, r]}

  describe "construction" do
    test "new/3 builds an equality" do
      eq = Equality.new(:int, lit(5), lit(5))
      assert Equality.equality?(eq)
    end

    test "equality?/1 rejects non-eq" do
      refute Equality.equality?({:list, :int})
      refute Equality.equality?(:any)
    end

    test "refl_type/2" do
      assert {:eq, :int, _, _} = Equality.refl_type(:int, lit(7))
    end
  end

  describe "check_refl/3" do
    test "ok when types match and a == b == x" do
      goal = Equality.new(:int, lit(5), lit(5))
      assert :ok = Equality.check_refl(goal, lit(5), :int)
    end

    test "fails on type mismatch" do
      goal = Equality.new(:int, lit(5), lit(5))
      assert {:error, _} = Equality.check_refl(goal, lit(5), :string)
    end

    test "fails on left-side mismatch" do
      goal = Equality.new(:int, lit(3), lit(5))
      assert {:error, _} = Equality.check_refl(goal, lit(5), :int)
    end
  end

  describe "rewrite/2" do
    test "substitutes the equal terms in goal" do
      eq = Equality.new(:int, var("a"), var("b"))

      goal = {:tuple, [], [var("a"), var("c")]}
      result = Equality.rewrite(eq, goal)
      assert {:tuple, _, [{:variable, _, "b"}, {:variable, _, "c"}]} = result
    end

    test "rewriting under a binary op" do
      eq = Equality.new(:int, lit(0), lit(0))
      goal = binop(:+, var("n"), lit(0))
      # 0 in goal becomes 0 (idempotent here, just exercising the walker)
      result = Equality.rewrite(eq, goal)
      assert {:binary_op, _, [{:variable, _, "n"}, _]} = result
    end

    test "rewrite is idempotent on non-matching goals" do
      eq = Equality.new(:int, var("a"), var("b"))
      goal = lit(42)
      assert ^goal = Equality.rewrite(eq, goal)
    end
  end

  describe "runtime erasure" do
    test "refl_runtime_value/0 is a stable atom" do
      assert :cure_refl == Equality.refl_runtime_value()
    end
  end
end
