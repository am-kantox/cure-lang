defmodule Cure.REPL.HistoryTest do
  use ExUnit.Case, async: true

  alias Cure.REPL.History

  setup do
    tmp = Path.join(System.tmp_dir!(), "cure-repl-history-#{System.unique_integer([:positive])}")
    on_exit(fn -> File.rm_rf(tmp) end)
    {:ok, tmp: tmp}
  end

  test "append is deduped against the immediately preceding entry", %{tmp: tmp} do
    h =
      History.load(tmp)
      |> History.append("foo")
      |> History.append("foo")
      |> History.append("bar")

    assert History.entries(h) == ["foo", "bar"]
  end

  test "append skips empty entries", %{tmp: tmp} do
    h = History.load(tmp) |> History.append("") |> History.append("foo")
    assert History.entries(h) == ["foo"]
  end

  test "prev walks from newest to oldest; next walks back", %{tmp: tmp} do
    h =
      History.load(tmp)
      |> History.append("one")
      |> History.append("two")
      |> History.append("three")

    assert {:ok, "three", h1} = History.prev(h, "")
    assert {:ok, "two", h2} = History.prev(h1, "")
    assert {:ok, "one", h3} = History.prev(h2, "")
    assert :at_top = History.prev(h3, "")

    assert {:ok, "two", h4} = History.next(h3)
    assert {:ok, "three", h5} = History.next(h4)
    assert {:ok, "", _h6} = History.next(h5)
  end

  test "draft is restored when stepping past newest", %{tmp: tmp} do
    h = History.load(tmp) |> History.append("stored")
    {:ok, _, h1} = History.prev(h, "draft-text")
    assert {:ok, "draft-text", _} = History.next(h1)
  end

  test "find_prev locates the most recent match", %{tmp: tmp} do
    h =
      History.load(tmp)
      |> History.append("foo")
      |> History.append("bar baz")
      |> History.append("quux")

    assert {:ok, "bar baz", pos} = History.find_prev(h, "bar", 0)
    assert pos == 2
  end

  test "persist round-trips through the file", %{tmp: tmp} do
    History.load(tmp)
    |> History.append("alpha")
    |> History.append("beta")

    reloaded = History.load(tmp)
    assert History.entries(reloaded) == ["alpha", "beta"]
  end

  test "grep is case-insensitive", %{tmp: tmp} do
    h =
      History.load(tmp)
      |> History.append("hello World")
      |> History.append("goodbye")

    assert ["hello World"] = History.grep(h, "WORLD")
  end
end
