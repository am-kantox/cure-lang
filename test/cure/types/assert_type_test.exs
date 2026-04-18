defmodule Cure.Types.AssertTypeTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler

  defp compile(source) do
    Compiler.compile_and_load(source, emit_events: false, check_types: true)
  end

  describe "assert_type expr : T" do
    test "passes when expression matches declared type" do
      source = """
      mod AssertType.Ok
        fn answer() -> Int = assert_type 42 : Int
      """

      {:ok, mod} = compile(source)
      assert mod.answer() == 42
    end

    test "wrapper is dropped at runtime" do
      source = """
      mod AssertType.Runtime
        fn doubled(n: Int) -> Int = assert_type n * 2 : Int
      """

      {:ok, mod} = compile(source)
      assert mod.doubled(21) == 42
    end

    test "fails to type check when types disagree" do
      source = """
      mod AssertType.Bad
        fn f() -> String = assert_type 42 : String
      """

      assert {:error, _} = compile(source)
    end
  end
end
