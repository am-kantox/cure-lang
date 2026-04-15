defmodule Cure.Compiler.ErrorsTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors

  describe "type errors" do
    test "type mismatch" do
      err = {:type_mismatch, "declared return type Int but body has type String", line: 3}
      result = Errors.format_error(err, "hello.cure")
      assert result =~ "error: type mismatch"
      assert result =~ "hello.cure:3"
      assert result =~ "declared return type Int"
    end

    test "unbound variable" do
      err = {:unbound_variable, "undefined variable 'x'", line: 5}
      result = Errors.format_error(err, "test.cure")
      assert result =~ "unbound variable"
      assert result =~ "test.cure:5"
      assert result =~ "undefined variable 'x'"
    end

    test "arity mismatch" do
      err = {:arity_mismatch, "function 'f' expects 2 arguments, got 1", line: 7}
      result = Errors.format_error(err, "test.cure")
      assert result =~ "arity mismatch"
      assert result =~ "expects 2 arguments"
    end

    test "wrapped type_error list" do
      errs =
        {:type_error,
         [
           {:type_mismatch, "bad return type", line: 1},
           {:unbound_variable, "undefined 'y'", line: 2}
         ]}

      result = Errors.format_error(errs, "multi.cure")
      assert result =~ "type mismatch"
      assert result =~ "unbound variable"
    end
  end

  describe "parse errors" do
    test "unexpected token" do
      err = {:unexpected_token, :rbrace, 10, 5}
      result = Errors.format_error(err, "parse.cure")
      assert result =~ "unexpected token"
      assert result =~ "parse.cure:10"
      assert result =~ "rbrace"
    end

    test "expected token" do
      err = {:expected, :rparen, :got, :eof, 4, 12}
      result = Errors.format_error(err, "parse.cure")
      assert result =~ "syntax error"
      assert result =~ "expected rparen"
    end
  end

  describe "codegen errors" do
    test "expected module" do
      err = {:expected_module, :some_ast}
      result = Errors.format_error(err, "bad.cure")
      assert result =~ "codegen error"
      assert result =~ "expected a module definition"
    end

    test "unsupported container" do
      err = {:unsupported_container, :protocol}
      result = Errors.format_error(err, "bad.cure")
      assert result =~ "unsupported container type"
    end
  end

  describe "fsm verifier errors" do
    test "unreachable state" do
      err = {:unreachable_state, "state 'X' is not reachable", line: 1}
      result = Errors.format_error(err, "fsm.cure")
      assert result =~ "unreachable state"
      assert result =~ "state 'X'"
    end

    test "deadlock" do
      err = {:deadlock, "non-terminal state 'Sink' has no outgoing", line: 5}
      result = Errors.format_error(err, "fsm.cure")
      assert result =~ "deadlock"
      assert result =~ "Sink"
    end
  end

  describe "file errors" do
    test "file read error" do
      err = {:file_read_error, "/tmp/missing.cure", :enoent}
      result = Errors.format_error(err, "nofile")
      assert result =~ "file error"
      assert result =~ "/tmp/missing.cure"
    end
  end

  describe "catch-all" do
    test "unknown error" do
      result = Errors.format_error(:something_unexpected, "test.cure")
      assert result =~ "compilation error"
      assert result =~ "something_unexpected"
    end
  end
end
