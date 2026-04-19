defmodule Cure.Types.ByteSizeRefinementTest do
  @moduledoc """
  Tests for the v0.22.0 `byte_size` refinement support:

    * `Cure.SMT.Translator` speaks `byte_size/1` as an uninterpreted
      function and emits `(declare-fun byte_size (Int) Int)` when the
      query touches one or more `byte_size` calls.
    * `Cure.Types.PatternRefinement.narrow/2` attaches a
      `byte_size(rest) == byte_size(scrutinee) - sum_of_preceding_sizes`
      refinement to `rest::binary` tail segments.
  """
  use ExUnit.Case, async: true

  alias Cure.SMT.Translator
  alias Cure.Types.PatternRefinement
  alias Cure.Types.Refinement

  describe "SMT translator" do
    test "byte_size(x) translates to an uninterpreted function call" do
      ast =
        {:function_call, [name: "byte_size", line: 1], [{:variable, [line: 1], "x"}]}

      assert Translator.translate(ast) == "(byte_size x)"
    end

    test "generate_subtype_query prepends byte_size fun declaration" do
      pred1 =
        {:function_call, [name: "byte_size", line: 1], [{:variable, [line: 1], "x"}]}

      pred2 = pred1
      query = Translator.generate_subtype_query(pred1, pred2, "x", :int)
      assert String.contains?(query, "(declare-fun byte_size (Int) Int)")
      assert String.contains?(query, "(set-logic QF_UFLIA)")
    end

    test "queries without byte_size keep the QF_LIA logic" do
      ast =
        {:binary_op, [operator: :>, category: :comparison, line: 1],
         [{:variable, [line: 1], "x"}, {:literal, [subtype: :integer], 0}]}

      query = Translator.generate_query(ast)
      assert String.contains?(query, "(set-logic QF_LIA)")
      refute String.contains?(query, "byte_size")
    end
  end

  describe "PatternRefinement for rest::binary" do
    test "attaches byte_size refinement to rest with literal-size preceding" do
      # <<tag::8, len::16, rest::binary>>
      segments = [
        bin_segment("tag", type: :integer, size: lit(8)),
        bin_segment("len", type: :integer, size: lit(16)),
        bin_segment("rest", type: :binary)
      ]

      pattern = {:literal, [subtype: :bytes, line: 1], segments}

      {bindings, _} = PatternRefinement.narrow(pattern, :bitstring)
      assert Map.has_key?(bindings, "rest")
      rest_type = bindings["rest"]
      assert Refinement.refinement?(rest_type)
      assert Refinement.base_type(rest_type) == :bitstring
      assert Refinement.var_name(rest_type) == "__value__"

      pred = Refinement.predicate(rest_type)
      assert match?({:binary_op, _, _}, pred)
    end

    test "leaves plain binary tails without preceding segments as :bitstring-refined" do
      pattern =
        {:literal, [subtype: :bytes, line: 1], [bin_segment("rest", type: :binary)]}

      {bindings, _} = PatternRefinement.narrow(pattern, :bitstring)
      # Just a tail: byte_size(rest) == byte_size(scrutinee) - 0
      assert Map.has_key?(bindings, "rest")
    end
  end

  # -- helpers ----------------------------------------------------------------

  defp bin_segment(name, meta) do
    {:bin_segment, [line: 1] ++ meta, [{:variable, [line: 1], name}]}
  end

  defp lit(value) do
    {:literal, [subtype: :integer, line: 1], value}
  end
end
