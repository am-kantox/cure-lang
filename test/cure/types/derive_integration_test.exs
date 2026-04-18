defmodule Cure.Types.DeriveIntegrationTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler

  defp compile(source) do
    Compiler.compile_and_load(source, emit_events: false)
  end

  describe "@derive(...) wired through the codegen (v0.19.0)" do
    test "@derive(Show) synthesises a show/1 export" do
      source = """
      mod Derive.ShowOnly
        @derive(Show)
        rec Point
          x: Int
          y: Int
      """

      {:ok, mod} = compile(source)
      exports = mod.module_info(:exports)
      assert {:show, 1} in exports
    end

    test "@derive(Eq) gives a runnable eq/2" do
      source = """
      mod Derive.EqRun
        @derive(Eq)
        rec Pair
          a: Int
          b: Int
      """

      {:ok, mod} = compile(source)
      assert mod.eq(%{__struct__: :pair, a: 1, b: 2}, %{__struct__: :pair, a: 1, b: 2}) == true
      assert mod.eq(%{__struct__: :pair, a: 1, b: 2}, %{__struct__: :pair, a: 1, b: 3}) == false
    end

    test "@derive(Ord) gives a runnable compare/2" do
      source = """
      mod Derive.OrdRun
        @derive(Ord)
        rec Pair
          a: Int
          b: Int
      """

      {:ok, mod} = compile(source)
      a = %{__struct__: :pair, a: 1, b: 2}
      b = %{__struct__: :pair, a: 1, b: 3}
      assert mod.compare(a, a) == :eq
      assert mod.compare(a, b) == :lt
      assert mod.compare(b, a) == :gt
    end

    test "@derive(Show, Eq, Ord) synthesises all three" do
      source = """
      mod Derive.AllThree
        @derive(Show, Eq, Ord)
        rec Vec
          x: Int
          y: Int
      """

      {:ok, mod} = compile(source)
      exports = mod.module_info(:exports)
      assert {:show, 1} in exports
      assert {:eq, 2} in exports
      assert {:compare, 2} in exports
    end
  end
end
