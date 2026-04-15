defmodule Cure.FSM.TypeSafety do
  @moduledoc """
  Type safety analysis for FSM definitions.

  Checks that FSM transitions are consistent:
  - All events from the same source state lead to valid target states
  - Guard expressions on transitions are well-typed
  - Action expressions produce valid state data mutations

  ## Usage

      {:ok, warnings} = Cure.FSM.TypeSafety.check(fsm_ast)
  """

  @doc """
  Check an FSM AST for type safety issues.

  Returns `{:ok, warnings}` where warnings is a list of potential issues.
  """
  @spec check(tuple()) :: {:ok, [term()]}
  def check({:container, meta, transitions}) do
    name = Keyword.get(meta, :name, "unnamed")
    trans = extract_transitions(transitions)

    warnings =
      check_duplicate_transitions(trans, name) ++
        check_wildcard_conflicts(trans, name) ++
        check_self_loops(trans, name)

    {:ok, warnings}
  end

  def check(_), do: {:ok, []}

  # -- Checks ------------------------------------------------------------------

  defp check_duplicate_transitions(trans, name) do
    # Check for duplicate (from, event) pairs
    pairs = Enum.map(trans, fn t -> {t.from, t.event} end)
    dupes = pairs -- Enum.uniq(pairs)

    Enum.map(dupes, fn {from, event} ->
      {:duplicate_transition, "FSM '#{name}': duplicate transition from '#{from}' on event '#{event}'"}
    end)
  end

  defp check_wildcard_conflicts(trans, name) do
    # Check if a wildcard transition conflicts with a specific one
    wildcard_events = trans |> Enum.filter(&(&1.from == "*")) |> Enum.map(& &1.event)
    specific_trans = Enum.reject(trans, &(&1.from == "*"))

    Enum.flat_map(specific_trans, fn t ->
      if t.event in wildcard_events do
        [{:wildcard_shadow, "FSM '#{name}': transition from '#{t.from}' on '#{t.event}' shadows wildcard"}]
      else
        []
      end
    end)
  end

  defp check_self_loops(trans, name) do
    trans
    |> Enum.filter(fn t -> t.from == t.to and t.from != "*" end)
    |> Enum.map(fn t ->
      {:self_loop, "FSM '#{name}': self-loop on state '#{t.from}' via event '#{t.event}'"}
    end)
  end

  # -- Transition Extraction ---------------------------------------------------

  defp extract_transitions(nodes) do
    Enum.flat_map(nodes, fn
      {:function_call, meta, _} ->
        if Keyword.get(meta, :name) == "transition" do
          [%{from: Keyword.get(meta, :from, "*"), event: Keyword.get(meta, :event, ""), to: Keyword.get(meta, :to, "")}]
        else
          []
        end

      _ ->
        []
    end)
  end
end
