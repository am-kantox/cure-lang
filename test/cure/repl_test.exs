defmodule Cure.REPLTest do
  use ExUnit.Case, async: true

  import ExUnit.CaptureIO

  alias Cure.REPL

  describe "input classification" do
    test "complete inputs" do
      assert :complete = REPL.__classify_input__("1 + 1")
      assert :complete = REPL.__classify_input__("foo(bar)")
      assert :complete = REPL.__classify_input__("[1, 2, 3]")
    end

    test "lines ending with continuation tokens" do
      assert :continue = REPL.__classify_input__("if x > 0 then")
      assert :continue = REPL.__classify_input__("fn(x) ->")
      assert :continue = REPL.__classify_input__("let x =")
      assert :continue = REPL.__classify_input__("if x > 0 then y else")
    end

    test "match-style with pipe" do
      assert :continue = REPL.__classify_input__("match x |")
    end

    test "trailing comma and open paren" do
      assert :continue = REPL.__classify_input__("f(a,")
      assert :continue = REPL.__classify_input__("f(")
    end
  end

  describe "error formatting" do
    test "string passes through" do
      assert "boom" = REPL.__format_error__("boom")
    end

    test "structured tuple is human-readable" do
      assert "parse: oops" = REPL.__format_error__({:parse, "oops", []})
    end

    test "fallback uses inspect" do
      assert REPL.__format_error__({:weird, 42}) =~ "weird"
    end
  end

  describe "error_device option" do
    test "defaults to :stderr so the standalone REPL keeps stream separation" do
      state = REPL.__new_state__()

      assert state.error_device == :stderr

      captured =
        capture_io(:stderr, fn ->
          REPL.__render_error__(state, "kaboom")
        end)

      assert captured =~ "error: kaboom"
    end

    test ":stdio routes diagnostics through the group leader" do
      state = REPL.__new_state__(error_device: :stdio)

      captured =
        capture_io(fn ->
          REPL.__render_error__(state, "kaboom")
        end)

      assert captured =~ "error: kaboom"
    end
  end
end
