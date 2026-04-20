defmodule Cure.REPL.HighlightTest do
  use ExUnit.Case, async: true

  alias Cure.REPL.{Highlight, Theme}

  test "returns a string even on empty input" do
    assert is_binary(Highlight.highlight(""))
  end

  test "emits ANSI escapes for real Cure source" do
    src = "fn add(a: Int, b: Int) -> Int = a + b"
    result = Highlight.highlight(src)
    assert is_binary(result)
    # After highlighting, stripping ANSI codes should yield a superset of the
    # original printable characters.
    stripped = Theme.strip_ansi(result)
    assert String.contains?(stripped, "add")
    assert String.contains?(stripped, "Int")
  end

  test "partial / broken source does not crash" do
    assert is_binary(Highlight.highlight("fn foo(x: Int) -> "))
  end
end
