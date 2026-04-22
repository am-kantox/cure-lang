defmodule Cure.REPLTest do
  # async: false -- the `describe "definitions"` block loads the shared
  # `:"Cure.Repl.Session"` BEAM module into the VM, which is process-global.
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  alias Cure.REPL
  alias Cure.REPL.Session

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

  describe "definitions" do
    setup do
      Session.clear()
      on_exit(&Session.clear/0)
      :ok
    end

    test "fn submission installs the definition and prints `defined name/arity`" do
      {state, stdout, _stderr} =
        submit_capture(REPL.__new_state__(), "fn add(a: Int, b: Int) -> Int = a + b")

      assert [%{key: {:fn, "add", 2, :public}}] = state.defs
      assert stdout =~ "defined add/2"
      assert function_exported?(Session.module_atom(), :add, 2)
    end

    test "follow-up expression can call the user-defined function" do
      state =
        REPL.__new_state__()
        |> submit("fn add(a: Int, b: Int) -> Int = a + b")

      {_state, stdout, _stderr} = submit_capture(state, "add(2, 3)")
      assert stdout =~ "=> 5"
    end

    test "redefining a function replaces the previous entry in place" do
      state =
        REPL.__new_state__()
        |> submit("fn answer() -> Int = 1")
        |> submit("fn other() -> Int = 2")

      assert [%{key: {:fn, "answer", 0, :public}}, %{key: {:fn, "other", 0, :public}}] =
               state.defs

      {state, stdout, _stderr} = submit_capture(state, "fn answer() -> Int = 42")

      assert stdout =~ "redefined answer/0"

      assert [%{key: {:fn, "answer", 0, :public}, source: "fn answer() -> Int = 42"}, _other] =
               state.defs

      {_state, stdout, _stderr} = submit_capture(state, "answer()")
      assert stdout =~ "=> 42"
    end

    test ":reset clears defs and unloads the session module" do
      state =
        REPL.__new_state__()
        |> submit("fn ping() -> Int = 1")

      assert [_] = state.defs
      assert :code.is_loaded(Session.module_atom())

      state = REPL.__submit__(state, ":reset")

      assert state.defs == []
      refute :code.is_loaded(Session.module_atom())
    end

    test ":defs command lists installed definitions" do
      state =
        REPL.__new_state__()
        |> submit("fn foo(x: Int) -> Int = x")
        |> submit("type Color = Red | Green")

      {_state, stdout, _stderr} = submit_capture(state, ":defs")

      assert stdout =~ "session definitions (2)"
      assert stdout =~ "foo/1"
      assert stdout =~ "type Color"
    end
  end

  # Feed `line` through the REPL pipeline, silencing any captured IO. Used
  # for setup steps whose stdout/stderr is not the subject of the
  # assertion.
  defp submit(state, line) do
    {next_state, _stdout, _stderr} = submit_capture(state, line)
    next_state
  end

  # Feed `line` through the REPL pipeline and return the updated state
  # along with the captured stdout and stderr.
  defp submit_capture(state, line) do
    parent = self()
    ref = make_ref()

    stderr =
      capture_io(:stderr, fn ->
        stdout =
          capture_io(fn ->
            send(parent, {ref, REPL.__submit__(state, line)})
          end)

        send(parent, {ref, :stdout, stdout})
      end)

    next_state =
      receive do
        {^ref, %Cure.REPL{} = s} -> s
      after
        0 -> raise "submit_capture/2 did not produce a REPL state"
      end

    stdout =
      receive do
        {^ref, :stdout, s} -> s
      after
        0 -> ""
      end

    {next_state, stdout, stderr}
  end
end
