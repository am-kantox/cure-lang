defmodule Cure.REPL.MarkdownTest do
  use ExUnit.Case, async: true

  alias Cure.REPL.{Markdown, Theme}

  defp mono, do: Theme.for_name(:mono)
  defp dark, do: Theme.for_name(:dark)

  test "passes through plain text untouched in mono" do
    assert Markdown.render("hello", mono()) == "hello"
  end

  test "renders headings and bullets without crashing in dark theme" do
    out = Markdown.render("# Title\n\n- one\n- two\n", dark())
    assert out =~ "Title"
    assert out =~ "one"
    assert out =~ "two"
  end

  test "renders fenced code blocks" do
    out = Markdown.render("```cure\nfn id(x) = x\n```", mono())
    assert out =~ "fn id(x) = x"
    # The fence markers themselves should be stripped.
    refute out =~ "```"
  end

  test "renders numbered lists" do
    out = Markdown.render("1. first\n2. second\n", mono())
    assert out =~ "first"
    assert out =~ "second"
  end

  test "renders inline links as `text (url)`" do
    out = Markdown.render("see [docs](https://example.com) here", mono())
    assert out =~ "docs"
    assert out =~ "(https://example.com)"
  end

  test "blank-line separation is preserved" do
    out = Markdown.render("one\n\ntwo", mono())
    assert out == "one\n\ntwo"
  end
end
