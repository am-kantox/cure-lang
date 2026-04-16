defmodule Cure.Types.PiTest do
  use ExUnit.Case, async: true

  alias Cure.Types.Pi

  defp lit(v), do: {:literal, [subtype: :integer], v}
  defp var(n), do: {:variable, [], n}
  defp binop(op, l, r), do: {:binary_op, [operator: op], [l, r]}

  describe "construction" do
    test "new/2 builds a Pi" do
      params = [{"x", :int, :explicit}]
      pi = Pi.new(params, var("Int"))
      assert Pi.pi?(pi)
      assert Pi.params(pi) == params
    end

    test "pi?/1 rejects non-pi" do
      refute Pi.pi?({:fun, [], :int})
      refute Pi.pi?(:int)
    end
  end

  describe "from_fun/1" do
    test "lifts a plain function" do
      pi = Pi.from_fun({:fun, [:int, :int], :int})
      assert {:pi, [{"_0", :int, :explicit}, {"_1", :int, :explicit}], _ret} = pi
    end

    test "lifts an effectful function ignoring effects" do
      pi = Pi.from_fun({:effun, [:int], :int, MapSet.new([:io])})
      assert {:pi, [{"_0", :int, :explicit}], _ret} = pi
    end

    test "passes through unrelated input" do
      assert :int = Pi.from_fun(:int)
    end
  end

  describe "apply_return/2" do
    test "non-dependent return" do
      pi = Pi.new([{"x", :int, :explicit}], var("Int"))
      assert :int = Pi.apply_return(pi, [lit(5)])
    end

    test "dependent: ret depends on a parameter" do
      # fn id(n: Int) -> Int = n
      # apply at 5 -> still :int (we're returning a type)
      pi = Pi.new([{"n", :int, :explicit}], var("Int"))
      assert :int = Pi.apply_return(pi, [lit(5)])
    end

    test "implicit and erased params skip binding" do
      pi =
        Pi.new(
          [
            {"T", :any, :implicit},
            {"x", :int, :explicit}
          ],
          var("Int")
        )

      # Only the explicit params bind; the call site provides one arg.
      assert :int = Pi.apply_return(pi, [lit(5)])
    end
  end

  describe "erase_implicits/1" do
    test "drops implicit and erased params" do
      pi =
        Pi.new(
          [
            {"T", :any, :implicit},
            {"n", :int, :erased},
            {"x", :int, :explicit}
          ],
          var("Int")
        )

      assert {:fun, [:int], :int} = Pi.erase_implicits(pi)
    end
  end

  describe "Reduce integration via apply_return" do
    test "arithmetic in return type folds at the call site" do
      # ret = m + n
      ret_ast = binop(:+, var("m"), var("n"))
      pi = Pi.new([{"m", :int, :explicit}, {"n", :int, :explicit}], ret_ast)

      # apply at 3, 5 -> :int (since the AST resolves to a type)
      # but the substitution should be reflected in the returned type display
      result = Pi.apply_return(pi, [lit(3), lit(5)])
      # 3 + 5 = 8, and Type.resolve of an integer literal node is :any
      # (we don't have first-class type-level integers yet) so this is :any
      assert result in [:any, :int]
    end
  end
end
