defmodule CureSite.MarkdownConverterTest do
  use ExUnit.Case, async: true

  alias CureSite.MarkdownConverter

  test "renders brace interpolation inside fenced cure blocks" do
    html =
      MarkdownConverter.to_html(~S"""
      ```cure
      "hello #{name}"
      "result: #{compute(42)}"
      ```
      """)

    assert html =~ ~S|#{|
    assert html =~ "compute"
    refute html =~ "&lbrace;"
    refute html =~ "&rbrace;"
  end
end
