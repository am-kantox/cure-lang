defmodule CureExampleTest do
  use ExUnit.Case, async: true

  describe "Greeter (cure module)" do
    test "hello/1 greets by name" do
      assert :greeter.hello("World") == "Hello, World!"
    end

    test "farewell/1 says goodbye" do
      assert :greeter.farewell("Cure") == "Goodbye, Cure. See you soon!"
    end
  end

  describe "Calculator (cure module)" do
    test "basic arithmetic" do
      assert :calculator.add(2, 3) == 5
      assert :calculator.sub(10, 4) == 6
      assert :calculator.mul(6, 7) == 42
    end

    test "factorial/1 with pattern matching" do
      assert :calculator.factorial(0) == 1
      assert :calculator.factorial(1) == 1
      assert :calculator.factorial(5) == 120
      assert :calculator.factorial(10) == 3_628_800
    end

    test "fibonacci/1 with multi-clause patterns" do
      assert :calculator.fibonacci(0) == 0
      assert :calculator.fibonacci(1) == 1
      assert :calculator.fibonacci(10) == 55
    end

    test "classify/1 with guards" do
      assert :calculator.classify(42) == "positive"
      assert :calculator.classify(-1) == "negative"
      assert :calculator.classify(0) == "zero"
    end

    test "safe_divide/2 returns Result tuples" do
      assert {:ok, 5} = :calculator.safe_divide(10, 2)
      assert {:error, "division by zero"} = :calculator.safe_divide(10, 0)
    end
  end

  describe "CureExample wrapper" do
    test "delegates to cure modules" do
      assert CureExample.greet("Test") == "Hello, Test!"
      assert CureExample.factorial(5) == 120
      assert CureExample.fibonacci(10) == 55
      assert CureExample.classify(0) == "zero"
      assert {:ok, 5} = CureExample.safe_divide(10, 2)
    end
  end
end
