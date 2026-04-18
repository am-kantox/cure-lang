defmodule Cure.Compiler.CommentPreservationTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}

  describe "lexer: preserve_comments (default off)" do
    test "plain # comments are discarded by default" do
      {:ok, tokens} = Lexer.tokenize("x = 1 # tail\ny = 2", emit_events: false)

      refute Enum.any?(tokens, &(&1.type == :line_comment))
    end

    test "## doc comments are always preserved" do
      {:ok, tokens} = Lexer.tokenize("## hello\nx = 1", emit_events: false)

      assert Enum.any?(tokens, &(&1.type == :doc_comment))
    end
  end

  describe "lexer: preserve_comments: true" do
    test "plain # comments become :line_comment tokens" do
      {:ok, tokens} =
        Lexer.tokenize(
          "x = 1 # a trailing note\ny = 2",
          emit_events: false,
          preserve_comments: true
        )

      line_comments =
        Enum.filter(tokens, &(&1.type == :line_comment))

      assert [%{value: "a trailing note"}] = line_comments
    end

    test "leading # on own line is preserved" do
      source = """
      # header comment
      x = 1
      """

      {:ok, tokens} =
        Lexer.tokenize(source, emit_events: false, preserve_comments: true)

      assert Enum.any?(tokens, fn t ->
               t.type == :line_comment and t.value == "header comment"
             end)
    end

    test "## and plain # coexist" do
      source = """
      ## a doc
      # and a note
      x = 1
      """

      {:ok, tokens} =
        Lexer.tokenize(source, emit_events: false, preserve_comments: true)

      assert Enum.any?(tokens, &(&1.type == :doc_comment))
      assert Enum.any?(tokens, &(&1.type == :line_comment))
    end
  end

  describe "parser: {:comment, ...} AST nodes" do
    test "top-level # comment produces a {:comment, meta, text} sibling" do
      source = """
      # hello
      x = 1
      """

      {:ok, tokens} =
        Lexer.tokenize(source, emit_events: false, preserve_comments: true)

      {:ok, ast} = Parser.parse(tokens, emit_events: false)

      assert {:block, _, children} = ast
      assert [_, _ | _] = children

      assert Enum.any?(children, fn
               {:comment, _, "hello"} -> true
               _ -> false
             end)
    end

    test "block-body # comment is kept as sibling, does not derail parsing" do
      source = """
      mod Demo
        # explain foo
        fn foo() -> Int = 1
      """

      {:ok, tokens} =
        Lexer.tokenize(source, emit_events: false, preserve_comments: true)

      {:ok, ast} = Parser.parse(tokens, emit_events: false)

      # Walk into the module body.
      {:container, _meta, body} = ast

      assert Enum.any?(body, fn
               {:comment, _, "explain foo"} -> true
               _ -> false
             end)

      assert Enum.any?(body, fn
               {:function_def, meta, _} -> Keyword.get(meta, :name) == "foo"
               _ -> false
             end)
    end

    test "inline # comment in expression position is treated as trivia" do
      source = """
      mod Demo
        fn foo() -> Int =
          1 # inline
      """

      {:ok, tokens} =
        Lexer.tokenize(source, emit_events: false, preserve_comments: true)

      assert {:ok, _ast} = Parser.parse(tokens, emit_events: false)
    end

    test "comments do not break type checking" do
      source = """
      mod Demo
        # greeting
        fn foo() -> Int = 42
      """

      {:ok, tokens} =
        Lexer.tokenize(source, emit_events: false, preserve_comments: true)

      {:ok, ast} = Parser.parse(tokens, emit_events: false)

      assert {:ok, _} = Cure.Types.Checker.check_module(ast, emit_events: false)
    end
  end
end
