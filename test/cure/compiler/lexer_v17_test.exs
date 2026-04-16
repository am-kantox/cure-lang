defmodule Cure.Compiler.LexerV17Test do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Lexer

  describe "fenced ### ... ### docstrings" do
    test "produces a single doc_comment with stripped common indent" do
      src = """
      mod M
        ###
        line one
        line two
        ###
        fn f() -> Int = 0
      """

      {:ok, tokens} = Lexer.tokenize(src, emit_events: false)

      docs = Enum.filter(tokens, fn t -> t.type == :doc_comment end)
      assert [%{value: value}] = docs
      assert value == "line one\nline two"
    end

    test "multiple fenced blocks produce multiple doc_comment tokens" do
      src = """
      mod M
        ###
        first
        ###
        fn a() -> Int = 0

        ###
        second
        ###
        fn b() -> Int = 0
      """

      {:ok, tokens} = Lexer.tokenize(src, emit_events: false)

      values = tokens |> Enum.filter(&(&1.type == :doc_comment)) |> Enum.map(& &1.value)
      assert values == ["first", "second"]
    end

    test "fenced doc emits dedents before the token" do
      src = """
      mod M
        fn a(n: Int) -> Int
          | 0 -> 0
          | n -> n
        ###
        doc for b
        ###
        fn b() -> Int = 0
      """

      {:ok, tokens} = Lexer.tokenize(src, emit_events: false)
      types = Enum.map(tokens, & &1.type)

      # A dedent must appear before the doc_comment (closing the `| n -> n`
      # clause block) so the doc belongs to the outer `mod` body, not to
      # the inner multi-clause body.
      doc_idx = Enum.find_index(types, &(&1 == :doc_comment))
      dedent_before? = types |> Enum.take(doc_idx) |> Enum.member?(:dedent)
      assert dedent_before?, "expected :dedent before :doc_comment"
    end
  end

  describe "?-suffixed identifiers" do
    test "predicate names lex as single identifiers" do
      {:ok, tokens} = Lexer.tokenize("fn even?(n: Int) -> Bool = 0", emit_events: false)

      identifiers =
        tokens
        |> Enum.filter(&(&1.type == :identifier))
        |> Enum.map(& &1.value)

      assert "even?" in identifiers
    end

    test "no gobbling -- `foo` before `?bar` stays one identifier" do
      # A trailing `?` is consumed only when what follows is NOT an
      # identifier-starter. When it *is* (e.g. `?bar`), the `?` is
      # left alone so the `?name` hole form can be handled elsewhere.
      case Lexer.tokenize("foo ?bar", emit_events: false) do
        {:ok, tokens} ->
          refute Enum.any?(tokens, fn t -> t.value == "foo?bar" end)

        {:error, _} ->
          :ok
      end
    end
  end
end
