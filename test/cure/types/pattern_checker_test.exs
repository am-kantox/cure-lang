defmodule Cure.Types.PatternCheckerTest do
  use ExUnit.Case, async: true

  alias Cure.Types.PatternChecker

  # -- AST Helpers -------------------------------------------------------------

  defp var(name), do: {:variable, [scope: :local], name}
  defp wildcard, do: {:variable, [scope: :local], "_"}
  defp bool_lit(v), do: {:literal, [subtype: :boolean], v}
  defp int_lit(v), do: {:literal, [subtype: :integer], v}
  defp string_lit(v), do: {:literal, [subtype: :string], v}
  defp atom_lit(v), do: {:literal, [subtype: :symbol], v}

  defp constructor(name, args \\ []) do
    {:function_call, [name: name], args}
  end

  defp empty_list, do: {:list, [], []}
  defp cons_list, do: {:list, [cons: true], [var("h"), var("t")]}
  defp tuple_pat(n), do: {:tuple, [], List.duplicate(var("_"), n)}

  # ============================================================================
  # Pattern Classification
  # ============================================================================

  describe "classify_pattern" do
    test "wildcard" do
      assert PatternChecker.classify_pattern(wildcard()) == :wildcard
    end

    test "named variable is wildcard" do
      assert PatternChecker.classify_pattern(var("x")) == :wildcard
    end

    test "boolean literal" do
      assert PatternChecker.classify_pattern(bool_lit(true)) == {:literal, :boolean, true}
      assert PatternChecker.classify_pattern(bool_lit(false)) == {:literal, :boolean, false}
    end

    test "integer literal" do
      assert PatternChecker.classify_pattern(int_lit(42)) == {:literal, :integer, 42}
    end

    test "constructor" do
      assert PatternChecker.classify_pattern(constructor("Ok", [var("x")])) == {:constructor, "Ok", 1}
      assert PatternChecker.classify_pattern(constructor("None")) == {:constructor, "None", 0}
    end

    test "empty list" do
      assert PatternChecker.classify_pattern(empty_list()) == :empty_list
    end

    test "cons list" do
      assert PatternChecker.classify_pattern(cons_list()) == :cons
    end

    test "tuple" do
      assert PatternChecker.classify_pattern(tuple_pat(2)) == {:tuple, 2}
    end
  end

  # ============================================================================
  # Bool Exhaustiveness
  # ============================================================================

  describe "Bool exhaustiveness" do
    test "true + false is exhaustive" do
      result = PatternChecker.check_match(:bool, [bool_lit(true), bool_lit(false)])
      assert result == :exhaustive
    end

    test "false + true is exhaustive (order independent)" do
      result = PatternChecker.check_match(:bool, [bool_lit(false), bool_lit(true)])
      assert result == :exhaustive
    end

    test "only true is non-exhaustive" do
      result = PatternChecker.check_match(:bool, [bool_lit(true)])
      assert {:non_exhaustive, missing} = result
      assert "false" in missing
    end

    test "only false is non-exhaustive" do
      result = PatternChecker.check_match(:bool, [bool_lit(false)])
      assert {:non_exhaustive, missing} = result
      assert "true" in missing
    end

    test "wildcard makes it exhaustive" do
      result = PatternChecker.check_match(:bool, [bool_lit(true), wildcard()])
      assert result == :exhaustive
    end

    test "variable makes it exhaustive" do
      result = PatternChecker.check_match(:bool, [var("x")])
      assert result == :exhaustive
    end
  end

  # ============================================================================
  # Result ADT Exhaustiveness
  # ============================================================================

  describe "Result ADT exhaustiveness" do
    test "Ok + Error is exhaustive" do
      patterns = [constructor("Ok", [var("v")]), constructor("Error", [var("e")])]
      result = PatternChecker.check_match({:adt, :result, [:any, :any]}, patterns)
      assert result == :exhaustive
    end

    test "only Ok is non-exhaustive" do
      patterns = [constructor("Ok", [var("v")])]
      result = PatternChecker.check_match({:adt, :result, [:any, :any]}, patterns)
      assert {:non_exhaustive, missing} = result
      assert "Error(...)" in missing
    end

    test "only Error is non-exhaustive" do
      patterns = [constructor("Error", [var("e")])]
      result = PatternChecker.check_match({:adt, :result, [:any, :any]}, patterns)
      assert {:non_exhaustive, missing} = result
      assert "Ok(...)" in missing
    end

    test "wildcard covers Result" do
      result = PatternChecker.check_match({:adt, :result, [:any, :any]}, [wildcard()])
      assert result == :exhaustive
    end
  end

  # ============================================================================
  # Option ADT Exhaustiveness
  # ============================================================================

  describe "Option ADT exhaustiveness" do
    test "Some + None is exhaustive" do
      patterns = [constructor("Some", [var("v")]), constructor("None")]
      result = PatternChecker.check_match({:adt, :option, [:any]}, patterns)
      assert result == :exhaustive
    end

    test "only Some is non-exhaustive" do
      patterns = [constructor("Some", [var("v")])]
      result = PatternChecker.check_match({:adt, :option, [:any]}, patterns)
      assert {:non_exhaustive, missing} = result
      assert "None" in missing
    end

    test "only None is non-exhaustive" do
      patterns = [constructor("None")]
      result = PatternChecker.check_match({:adt, :option, [:any]}, patterns)
      assert {:non_exhaustive, missing} = result
      assert "Some(...)" in missing
    end
  end

  # ============================================================================
  # List Exhaustiveness
  # ============================================================================

  describe "List exhaustiveness" do
    test "[] + [h|t] is exhaustive" do
      result = PatternChecker.check_match({:list, :int}, [empty_list(), cons_list()])
      assert result == :exhaustive
    end

    test "only [] is non-exhaustive" do
      result = PatternChecker.check_match({:list, :int}, [empty_list()])
      assert {:non_exhaustive, missing} = result
      assert "[_ | _]" in missing
    end

    test "only [h|t] is non-exhaustive" do
      result = PatternChecker.check_match({:list, :int}, [cons_list()])
      assert {:non_exhaustive, missing} = result
      assert "[]" in missing
    end

    test "wildcard covers List" do
      result = PatternChecker.check_match({:list, :int}, [wildcard()])
      assert result == :exhaustive
    end
  end

  # ============================================================================
  # Infinite Types
  # ============================================================================

  describe "infinite type exhaustiveness" do
    test "Int without wildcard is non-exhaustive" do
      result = PatternChecker.check_match(:int, [int_lit(0), int_lit(1)])
      assert {:non_exhaustive, _} = result
    end

    test "Int with wildcard is exhaustive" do
      result = PatternChecker.check_match(:int, [int_lit(0), wildcard()])
      assert result == :exhaustive
    end

    test "String without wildcard is non-exhaustive" do
      result = PatternChecker.check_match(:string, [string_lit("hello")])
      assert {:non_exhaustive, _} = result
    end

    test "Atom without wildcard is non-exhaustive" do
      result = PatternChecker.check_match(:atom, [atom_lit(:ok)])
      assert {:non_exhaustive, _} = result
    end

    test ":any without wildcard is non-exhaustive" do
      result = PatternChecker.check_match(:any, [int_lit(0)])
      assert {:non_exhaustive, _} = result
    end

    test ":any with wildcard is exhaustive" do
      result = PatternChecker.check_match(:any, [wildcard()])
      assert result == :exhaustive
    end
  end

  # ============================================================================
  # Multi-clause Functions
  # ============================================================================

  describe "multi-clause function exhaustiveness" do
    test "bool clauses with both values" do
      clause_patterns = [[bool_lit(true)], [bool_lit(false)]]
      result = PatternChecker.check_clauses(:bool, clause_patterns)
      assert result == :exhaustive
    end

    test "bool clauses missing false" do
      clause_patterns = [[bool_lit(true)]]
      result = PatternChecker.check_clauses(:bool, clause_patterns)
      assert {:non_exhaustive, missing} = result
      assert "false" in missing
    end

    test "clause with wildcard is exhaustive" do
      clause_patterns = [[int_lit(0)], [wildcard()]]
      result = PatternChecker.check_clauses(:int, clause_patterns)
      assert result == :exhaustive
    end
  end
end
