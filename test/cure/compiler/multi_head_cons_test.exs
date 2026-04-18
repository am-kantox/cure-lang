defmodule Cure.Compiler.MultiHeadConsTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler

  defp compile(source) do
    Compiler.compile_and_load(source, emit_events: false)
  end

  describe "multi-head cons patterns (v0.19.0)" do
    test "[a, b | rest] parses and matches the first two elements" do
      source = """
      mod Cons.Two
        fn first_two_sum(xs: List(Int), default: Int) -> Int =
          match xs
            [a, b | _rest] -> a + b
            _              -> default
      """

      {:ok, mod} = compile(source)
      assert mod.first_two_sum([1, 2, 3, 4], 0) == 3
      assert mod.first_two_sum([10, 20], 0) == 30
      assert mod.first_two_sum([5], 99) == 99
      assert mod.first_two_sum([], 99) == 99
    end

    test "[a, b, c | rest] binds three heads" do
      source = """
      mod Cons.Three
        fn sum_three(xs: List(Int), default: Int) -> Int =
          match xs
            [a, b, c | _rest] -> a + b + c
            _                 -> default
      """

      {:ok, mod} = compile(source)
      assert mod.sum_three([1, 2, 3, 4, 5], 0) == 6
      assert mod.sum_three([1, 2], 99) == 99
    end

    test "multi-head cons works in construction too" do
      source = """
      mod Cons.Build
        fn prepend_two(xs: List(Int)) -> List(Int) = [10, 20 | xs]
      """

      {:ok, mod} = compile(source)
      assert mod.prepend_two([1, 2, 3]) == [10, 20, 1, 2, 3]
    end
  end
end
