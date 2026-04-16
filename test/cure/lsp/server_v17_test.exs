defmodule Cure.LSP.ServerV17Test do
  use ExUnit.Case, async: true

  alias Cure.LSP.Server

  @sample """
  mod Demo
    fn add(a: Int, b: Int) -> Int = a + b
    fn double(x: Int) -> Int = x * 2
  """

  describe "compute_inlay_hints/1" do
    test "produces a hint per function definition" do
      hints = Server.compute_inlay_hints(@sample)
      assert is_list(hints)
      labels = Enum.map(hints, & &1["label"])
      assert Enum.any?(labels, fn l -> l =~ "fn add" end)
      assert Enum.any?(labels, fn l -> l =~ "fn double" end)
    end
  end

  describe "compute_signature_help/3" do
    test "returns nil away from a call site" do
      assert nil == Server.compute_signature_help("not a function", 0, 5)
    end
  end

  describe "compute_formatting_edits/1" do
    test "returns one full-document edit on parseable text" do
      edits = Server.compute_formatting_edits(@sample)
      assert [%{"range" => _, "newText" => _}] = edits
    end

    test "handles unparseable input without crashing" do
      # The parser is tolerant enough to turn lone tokens into a small AST;
      # we only require the call to not raise and to return a list.
      assert is_list(Server.compute_formatting_edits("@@@@"))
    end
  end

  describe "prepare_rename/3" do
    test "returns the word range under the cursor" do
      result = Server.prepare_rename("  fn add(a: Int, b: Int) -> Int = a + b", 0, 6)
      assert %{"start" => _, "end" => _} = result
    end
  end

  describe "compute_rename/5" do
    test "produces a workspace edit set" do
      result = Server.compute_rename("file://x", @sample, 1, 6, "plus")
      assert %{"changes" => %{"file://x" => edits}} = result
      assert is_list(edits)
    end
  end

  describe "compute_code_lenses/2" do
    test "lenses for every function" do
      lenses = Server.compute_code_lenses("file://x", @sample)
      titles = Enum.map(lenses, & &1["command"]["title"])
      assert Enum.all?(titles, &(&1 == "Type | Effects"))
    end
  end

  describe "compute_semantic_tokens/1" do
    test "produces an LSP token integer stream" do
      tokens = Server.compute_semantic_tokens(@sample)
      assert is_list(tokens)
      assert rem(length(tokens), 5) == 0
    end
  end

  describe "compute_workspace_symbols/2" do
    test "filters by query" do
      docs = %{"file://demo.cure" => @sample}
      assert symbols = Server.compute_workspace_symbols("add", docs)
      assert Enum.any?(symbols, fn s -> s["name"] == "add" end)
    end
  end
end
