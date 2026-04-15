defmodule Cure.Compiler.IntegrationTest do
  use ExUnit.Case, async: false

  # ============================================================================
  # End-to-end: Cure source -> compile -> load -> call
  # ============================================================================

  describe "end-to-end compilation" do
    test "simple arithmetic function" do
      source = """
      mod BasicMath
        fn add(a: Int, b: Int) -> Int = a + b
      """

      {:ok, module} = Cure.Compiler.compile_and_load(source)
      assert module == :"Cure.BasicMath"
      assert module.add(3, 4) == 7
    after
      purge(:"Cure.BasicMath")
    end

    test "function with multiple expressions in body" do
      source = """
      mod Calc
        fn double(x: Int) -> Int = x * 2
      """

      {:ok, module} = Cure.Compiler.compile_and_load(source)
      assert module.double(21) == 42
    after
      purge(:"Cure.Calc")
    end

    test "module with multiple functions" do
      source = """
      mod Arith
        fn add(a: Int, b: Int) -> Int = a + b
        fn sub(a: Int, b: Int) -> Int = a - b
        fn mul(a: Int, b: Int) -> Int = a * b
      """

      {:ok, module} = Cure.Compiler.compile_and_load(source)
      assert module.add(10, 5) == 15
      assert module.sub(10, 5) == 5
      assert module.mul(10, 5) == 50
    after
      purge(:"Cure.Arith")
    end

    test "@extern FFI to Erlang stdlib" do
      source = """
      mod ExtTest
        @extern(:erlang, :abs, 1)
        fn abs_val(n: Int) -> Int
      """

      {:ok, module} = Cure.Compiler.compile_and_load(source)
      assert module.abs_val(-42) == 42
      assert module.abs_val(42) == 42
    after
      purge(:"Cure.ExtTest")
    end

    test "conditional (if/else)" do
      source = """
      mod Logic
        fn max(a: Int, b: Int) -> Int = if a > b then a else b
      """

      {:ok, module} = Cure.Compiler.compile_and_load(source)
      assert module.max(3, 7) == 7
      assert module.max(10, 2) == 10
    after
      purge(:"Cure.Logic")
    end

    test "pattern matching" do
      source = """
      mod Matcher
        fn describe(x: Int) -> String
          | 0 -> "zero"
          | 1 -> "one"
          | _ -> "other"
      """

      {:ok, module} = Cure.Compiler.compile_and_load(source)
      assert module.describe(0) == "zero"
      assert module.describe(1) == "one"
      assert module.describe(99) == "other"
    after
      purge(:"Cure.Matcher")
    end

    test "let binding" do
      source = """
      mod Binding
        fn compute(x: Int) -> Int = let y = x * 2
      """

      {:ok, module} = Cure.Compiler.compile_and_load(source)
      # let y = x * 2 returns the match result which is x * 2
      assert module.compute(5) == 10
    after
      purge(:"Cure.Binding")
    end

    test "private function is not exported" do
      source = """
      mod Visibility
        fn public_fn() -> Int = 42
        local fn private_fn() -> Int = 99
      """

      {:ok, module} = Cure.Compiler.compile_and_load(source)
      assert module.public_fn() == 42

      # Private function should not be in exports
      exports = module.module_info(:exports)
      refute Enum.any?(exports, fn {name, _} -> name == :private_fn end)
    after
      purge(:"Cure.Visibility")
    end

    test "boolean operations" do
      source = """
      mod BoolTest
        fn both(a: Bool, b: Bool) -> Bool = a and b
        fn either(a: Bool, b: Bool) -> Bool = a or b
      """

      {:ok, module} = Cure.Compiler.compile_and_load(source)
      assert module.both(true, true) == true
      assert module.both(true, false) == false
      assert module.either(false, true) == true
      assert module.either(false, false) == false
    after
      purge(:"Cure.BoolTest")
    end

    test "comparison operations" do
      source = """
      mod CmpTest
        fn is_positive(x: Int) -> Bool = x > 0
      """

      {:ok, module} = Cure.Compiler.compile_and_load(source)
      assert module.is_positive(5) == true
      assert module.is_positive(-3) == false
    after
      purge(:"Cure.CmpTest")
    end

    test "lambda (anonymous function)" do
      source = """
      mod LambdaTest
        fn apply_fn(x: Int) -> Int = let f = fn(n) -> n * 2
      """

      {:ok, module} = Cure.Compiler.compile_and_load(source)
      # Returns the lambda itself as match result
      result = module.apply_fn(5)
      assert is_function(result, 1)
      assert result.(5) == 10
    after
      purge(:"Cure.LambdaTest")
    end
  end

  # Helper to unload a module
  defp purge(module) do
    :code.purge(module)
    :code.delete(module)
  end
end
