defmodule Cure.Doc.MarkdownTest do
  use ExUnit.Case, async: true

  alias Cure.Doc.Markdown

  test "nil / empty input yields empty string" do
    assert Markdown.to_html(nil) == ""
    assert Markdown.to_html("") == ""
  end

  test "renders headings, lists, and inline styling" do
    html = Markdown.to_html("# Title\n\n- _one_\n- *two*\n")
    assert html =~ "<h1>"
    assert html =~ "Title"
    assert html =~ "<ul>"
    # Md uses `*x*` for bold; `_x_` for italic.
    assert html =~ "<b>"
    assert html =~ "<i>"
  end

  test "highlights fenced cure blocks through Makeup" do
    html = Markdown.to_html("```cure\nfn id(x: T) -> T = x\n```")
    assert html =~ ~s(class="language-cure")
    assert html =~ "highlight"
  end

  test "passes through unknown languages without crashing" do
    html = Markdown.to_html("```ruby\nputs 'hi'\n```")
    assert html =~ ~s(class="language-ruby")
  end

  test "substitutes {{cure_version}} placeholders" do
    html = Markdown.to_html("Version {{cure_version}}, tag {{cure_vversion}}.")
    version = Cure.version()
    assert html =~ version
    assert html =~ "v" <> version
  end
end
