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

    test ":t reports the real return type for a session function" do
      state =
        REPL.__new_state__()
        |> submit("fn add1(a: Int, b: Int) -> Int = a + b")

      {_state, stdout, _stderr} = submit_capture(state, ":t add1(1, 2)")

      assert stdout =~ "add1(1, 2) : Int"
      refute stdout =~ ": Any"
    end
  end

  describe ":let meta-command" do
    setup do
      Session.clear()
      on_exit(&Session.clear/0)
      :ok
    end

    test "installs the bound value as a zero-arg session fn" do
      {state, stdout, _stderr} =
        submit_capture(REPL.__new_state__(), ":let answer = 42")

      assert [%{key: {:fn, "answer", 0, :public}, source: "fn answer() -> Any = 42"}] =
               state.defs

      assert stdout =~ "pinned answer/0 : () -> Int"
      assert function_exported?(Session.module_atom(), :answer, 0)
      # `apply/3` keeps the dynamic call off the compiler's radar so it does
      # not warn about `:"Cure.Repl.Session"` (which is defined at runtime).
      assert 42 = apply(Session.module_atom(), :answer, [])
    end

    test "let-bound value is reachable from a follow-up expression" do
      state =
        REPL.__new_state__()
        |> submit(":let a = 1")
        |> submit(":let b = a() + 1")

      {_state, stdout, _stderr} = submit_capture(state, "b()")
      assert stdout =~ "=> 2"
    end

    test "redefining a pinned binding replaces the entry in place" do
      state =
        REPL.__new_state__()
        |> submit(":let x = 1")

      {state, stdout, _stderr} = submit_capture(state, ":let x = 99")

      assert stdout =~ "redefined x/0"

      assert [%{key: {:fn, "x", 0, :public}, source: "fn x() -> Any = 99"}] = state.defs

      {_state, stdout, _stderr} = submit_capture(state, "x()")
      assert stdout =~ "=> 99"
    end

    test "rejects invalid identifiers" do
      {state, _stdout, stderr} =
        submit_capture(REPL.__new_state__(), ":let 1bad = 42")

      assert state.defs == []
      assert stderr =~ "invalid binding name"
    end

    test "reports a usage error on missing '='" do
      {state, _stdout, stderr} =
        submit_capture(REPL.__new_state__(), ":let foo")

      assert state.defs == []
      assert stderr =~ "usage: :let name = expr"
    end

    test "reports a usage error on an empty right-hand side" do
      {state, _stdout, stderr} =
        submit_capture(REPL.__new_state__(), ":let foo =")

      assert state.defs == []
      assert stderr =~ "usage: :let name = expr"
    end

    test ":defs lists pinned let bindings alongside explicit declarations" do
      state =
        REPL.__new_state__()
        |> submit(":let pi = 3.14")
        |> submit("fn square(x: Int) -> Int = x * x")

      {_state, stdout, _stderr} = submit_capture(state, ":defs")

      assert stdout =~ "session definitions (2)"
      assert stdout =~ "pi/0"
      assert stdout =~ "square/1"
    end
  end

  describe ":edit meta-command" do
    setup do
      Session.clear()
      on_exit(&Session.clear/0)
      :ok
    end

    test "runs $EDITOR and dispatches its contents as a fresh submission" do
      script_path = write_editor_stub("fn pinned() -> Int = 7")
      System.put_env("EDITOR", script_path)

      try do
        {state, stdout, _stderr} =
          submit_capture(REPL.__new_state__(), ":edit")

        assert stdout =~ "defined pinned/0"
        assert [%{key: {:fn, "pinned", 0, :public}}] = state.defs
        assert state.input_buffer == []
      after
        System.delete_env("EDITOR")
        File.rm(script_path)
      end
    end

    test "an empty editor buffer clears input_buffer and reports the no-op" do
      script_path = write_editor_stub("")
      System.put_env("EDITOR", script_path)

      try do
        {state, stdout, _stderr} =
          submit_capture(REPL.__new_state__(), ":edit")

        assert stdout =~ "empty buffer"
        assert state.input_buffer == []
      after
        System.delete_env("EDITOR")
        File.rm(script_path)
      end
    end

    test "a multi-line editor buffer evaluates the whole body, not just the first line" do
      # Regression test: the old evaluator spliced the source inline after
      # `fn main() -> Any = `, which left every line past the first at
      # column 0 -- siblings of `mod` instead of body statements of
      # `main/0`. Indenting the body under `main/0` lets the parser read
      # the whole thing as a block, so the REPL prints the result of the
      # final expression instead of only the first.
      script_path = write_editor_stub("let a = 1\nlet b = a + 1\nb")
      System.put_env("EDITOR", script_path)

      try do
        {_state, stdout, _stderr} =
          submit_capture(REPL.__new_state__(), ":edit")

        assert stdout =~ "=> 2"
      after
        System.delete_env("EDITOR")
        File.rm(script_path)
      end
    end

    test "a non-zero editor exit discards the buffer without submitting" do
      # The script exits non-zero *after* overwriting the tmp file, so we
      # verify the guard triggers on exit_code alone.
      script_path =
        write_editor_stub_raw("""
        #!/bin/sh
        echo 'fn would_define() -> Int = 1' > "$1"
        exit 3
        """)

      System.put_env("EDITOR", script_path)

      try do
        {state, _stdout, stderr} =
          submit_capture(REPL.__new_state__(), ":edit")

        assert stderr =~ "editor exited with status 3"
        assert state.defs == []
        assert state.input_buffer == []
      after
        System.delete_env("EDITOR")
        File.rm(script_path)
      end
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

  # Write an executable shell script that overwrites its first argument
  # (the REPL's temp file) with `content`. Returns the script path.
  defp write_editor_stub(content) when is_binary(content) do
    write_editor_stub_raw("""
    #!/bin/sh
    cat > "$1" <<'CURE_REPL_EDITOR_STUB_EOF'
    #{content}
    CURE_REPL_EDITOR_STUB_EOF
    """)
  end

  defp write_editor_stub_raw(script) when is_binary(script) do
    path =
      Path.join(
        System.tmp_dir!(),
        "cure-repl-edit-stub-#{System.unique_integer([:positive])}.sh"
      )

    File.write!(path, script)
    File.chmod!(path, 0o755)
    path
  end
end
