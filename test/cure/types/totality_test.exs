defmodule Cure.Types.TotalityTest do
  use ExUnit.Case, async: true

  alias Cure.Types.Totality

  defp lit(v), do: {:literal, [subtype: :integer], v}
  defp var(n), do: {:variable, [], n}
  defp binop(op, l, r), do: {:binary_op, [operator: op], [l, r]}

  describe "classify/1" do
    test "non-recursive single-clause function is total" do
      fn_def =
        {:function_def,
         [
           name: "double",
           params: [{:param, [type: var("Int")], "n"}],
           clauses: [],
           coverage: :complete
         ], binop(:*, var("n"), lit(2))}

      assert :total = Totality.classify(fn_def)
    end

    test "non-shrinking direct recursion is partial" do
      # fn loop(n: Int) = loop(n)
      body = {:function_call, [name: "loop"], [var("n")]}

      fn_def =
        {:function_def,
         [
           name: "loop",
           params: [{:param, [type: var("Int")], "n"}],
           clauses: [],
           coverage: :complete
         ], body}

      assert :partial = Totality.classify(fn_def)
    end

    test "shrinking recursion via n - 1 is total" do
      body = {:function_call, [name: "fact"], [binop(:-, var("n"), lit(1))]}

      clause =
        {:function_clause, [patterns: [var("n")]], [body]}

      fn_def =
        {:function_def, [name: "fact", params: [], clauses: [clause], coverage: :complete], body}

      assert :total = Totality.classify(fn_def)
    end

    test "non-function input gives :unknown" do
      assert :unknown = Totality.classify({:literal, [], 1})
    end
  end

  describe "total_required?/1" do
    test "detects @total true decorator" do
      meta = [decorator: {:total, [{:literal, [subtype: :boolean], true}]}]
      assert Totality.total_required?(meta)
    end

    test "detects @total decorator without explicit value" do
      meta = [decorator: {:total, []}]
      assert Totality.total_required?(meta)
    end

    test "absent decorator returns false" do
      assert false == Totality.total_required?([])
    end

    test "other decorators do not match" do
      meta = [decorator: {:deprecated, []}]
      refute Totality.total_required?(meta)
    end
  end
end
