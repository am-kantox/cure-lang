defmodule Cure.REPL.CompleterTest do
  use ExUnit.Case, async: true

  alias Cure.REPL.Completer

  describe "meta-command completion" do
    test "unique match extends the token" do
      assert {:unique, ":history"} = Completer.complete(":histo", 6)
    end

    test "multiple matches return partial prefix" do
      result = Completer.complete(":h", 2)
      assert match?({:partial, _, _}, result)
      {:partial, common, cands} = result
      assert String.starts_with?(common, ":h")
      assert ":help" in cands
      assert ":history" in cands
      assert ":h" in cands
    end

    test "no match returns :none" do
      assert :none = Completer.complete(":xyzxyz", 7)
    end
  end

  describe "keyword fallback" do
    test "partial Cure keyword completes uniquely" do
      assert {:unique, "match"} = Completer.complete("matc", 4)
    end
  end
end
