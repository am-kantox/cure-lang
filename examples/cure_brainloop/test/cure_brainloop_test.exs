defmodule CureBrainloopTest do
  use ExUnit.Case, async: true

  doctest CureBrainloop

  describe "eval/2 -- arithmetic" do
    test "evaluates a bare integer" do
      assert {:ok, 42} = CureBrainloop.eval("42")
    end

    test "honours operator precedence" do
      assert {:ok, 7} = CureBrainloop.eval("1 + 2 * 3")
    end

    test "respects parentheses" do
      assert {:ok, 9} = CureBrainloop.eval("(1 + 2) * 3")
    end

    test "division is integer" do
      assert {:ok, 3} = CureBrainloop.eval("7 / 2")
    end

    test "division by zero reports error" do
      assert {:error, :division_by_zero} = CureBrainloop.eval("1 / 0")
    end
  end

  describe "eval/2 -- let/if" do
    test "threads let bindings through the body" do
      assert {:ok, 5} = CureBrainloop.eval("let x = 2 in x * x + 1")
    end

    test "if-then-else dispatches on the guard value" do
      assert {:ok, 1} = CureBrainloop.eval("if 1 then 1 else 2")
      assert {:ok, 2} = CureBrainloop.eval("if 0 then 1 else 2")
    end

    test "nested let shadows outer bindings" do
      assert {:ok, 3} = CureBrainloop.eval("let x = 1 in let x = 3 in x")
    end

    test "undefined variable is an error" do
      assert {:error, :undefined_variable} = CureBrainloop.eval("nope")
    end
  end

  describe "eval/2 -- environment" do
    test "accepts a pre-populated environment" do
      assert {:ok, 10} = CureBrainloop.eval("x * 5", %{x: 2})
    end
  end
end
