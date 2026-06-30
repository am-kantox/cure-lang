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

    test "@extern untyped head (E056)" do
      err = {:extern_untyped_head, "@extern declarations must have a fully typed head; add a return type", line: 2}
      result = Errors.format_error(err, "ffi.cure")
      assert result =~ "@extern declaration missing a typed head (E056)"
      assert result =~ "ffi.cure:2"
      assert result =~ "fully typed head"
    end

    test "@extern has a body (E057)" do
      err = {:extern_has_body, "@extern declarations are type-only signatures and must not have a body", line: 3}
      result = Errors.format_error(err, "ffi.cure")
      assert result =~ "@extern declaration has a body (E057)"
      assert result =~ "ffi.cure:3"
      assert result =~ "must not have a body"
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

    test "raw list of errors is rendered directly (regression: used to hit inspect/1)" do
      # `Cure.Types.Checker.check_module/2` returns `{:error, errors}` with
      # `errors` being a bare list. The formatter must render each entry as
      # a proper diagnostic instead of dropping into the catch-all that just
      # inspects the list.
      errs = [
        {:type_mismatch, "bad return type", line: 1},
        {:unbound_variable, "undefined 'y'", line: 2}
      ]

      result = Errors.format_error(errs, "multi.cure")
      refute result =~ "compilation error"
      refute result =~ "error: error:"
      assert result =~ "error: type mismatch"
      assert result =~ "error: unbound variable"
      assert result =~ "multi.cure:1"
      assert result =~ "multi.cure:2"
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

  describe "@extern catalog entries" do
    for code <- ~w(E056 E057) do
      test "explain/#{code}" do
        assert {:ok, text} = Errors.explain(unquote(code))
        assert text =~ unquote(code)
        assert text =~ "@extern"
        assert text =~ "Fix:"
      end
    end
  end

  describe "tuple type deprecation catalog entry (E086)" do
    test "explain/E086 describes the %[A, B] migration" do
      assert {:ok, text} = Errors.explain("E086")
      assert text =~ "E086"
      assert text =~ "E-TYPE-TUPLE-PAREN"
      assert text =~ "%[A, B]"
      assert text =~ "Fix:"
    end

    test "E086 is case-insensitive like other codes" do
      assert {:ok, _text} = Errors.explain("e086")
    end
  end
end
