defmodule Cure.Types.TotalityMutualTest do
  use ExUnit.Case, async: true

  alias Cure.Types.Totality

  describe "check_mutual/1" do
    test "trivial module with no mutual recursion returns no SCCs" do
      stmts = [
        fn_def("a", ["b"], []),
        fn_def("b", [], [])
      ]

      assert Totality.check_mutual(stmts) == []
    end

    test "reports a suspect SCC for non-decreasing mutual recursion" do
      stmts = [
        fn_def("a", ["b"], []),
        fn_def("b", ["a"], [])
      ]

      assert [{cycle, :suspect}] = Totality.check_mutual(stmts)
      assert Enum.sort(cycle) == ["a", "b"]
    end

    test "marks the SCC :ok when at least one function has structural clauses" do
      # `a` has a multi-clause with a list pattern, which is a structural
      # base case. The cycle is therefore (conservatively) classified OK.
      stmts = [
        fn_def("a", ["b"],
          clauses: [
            %{params: [{:list, [], []}], guard: nil, body: []},
            %{params: [{:list, [cons: true], [{:variable, [], "h"}, {:variable, [], "t"}]}], guard: nil, body: []}
          ]
        ),
        fn_def("b", ["a"], [])
      ]

      assert [{_cycle, :ok}] = Totality.check_mutual(stmts)
    end

    test "ignores self-recursion (handled by classify/1, not SCC)" do
      # A single-node SCC is not a mutual cycle, so no entry is produced.
      stmts = [
        fn_def("factorial", ["factorial"], [])
      ]

      assert Totality.check_mutual(stmts) == []
    end
  end

  # -- helpers ----------------------------------------------------------------

  defp fn_def(name, callees, opts) do
    meta =
      [name: name, params: [], arity: 0, visibility: :public, line: 0]
      |> maybe_add_clauses(Keyword.get(opts, :clauses))

    body = Enum.map(callees, fn c -> {:function_call, [name: c], []} end)
    {:function_def, meta, body}
  end

  defp maybe_add_clauses(meta, nil), do: meta
  defp maybe_add_clauses(meta, clauses), do: Keyword.put(meta, :clauses, clauses)
end
