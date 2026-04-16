defmodule Cure.FSM.Verifier do
  @moduledoc """
  Structural verifier for Cure FSM definitions.

  Performs compile-time analysis on FSM MetaAST nodes without SMT:

  - **Reachability**: every declared state is reachable from the initial state.
  - **Deadlock freedom**: every non-terminal state has at least one outgoing transition.
  - **Terminal state validation**: `@terminal` states must exist in the transition graph.

  ## Pipeline Events

  Emits via `Cure.Pipeline.Events`:

  - `{:fsm_verifier, :verification_passed, name, meta}`
  - `{:fsm_verifier, :verification_failed, errors, meta}`
  - `{:fsm_verifier, :reachability_result, {state, reachable?}, meta}`
  - `{:fsm_verifier, :deadlock_check, {state, has_outgoing?}, meta}`
  """

  alias Cure.Pipeline.Events

  @doc """
  Verify an FSM MetaAST container node.

  Returns `{:ok, results}` where results is a list of check outcomes,
  or `{:error, errors}` if verification fails.
  """
  @spec verify(tuple(), keyword()) :: {:ok, list()} | {:error, list()}
  def verify(ast, opts \\ []) do
    emit? = Keyword.get(opts, :emit_events, true)
    file = Keyword.get(opts, :file, "nofile")

    {:container, meta, transitions} = ast
    name = Keyword.get(meta, :name, "unnamed")
    terminal_states = Keyword.get(meta, :terminal_states, [])
    on_transition_clauses = Keyword.get(meta, :on_transition, [])
    line = Keyword.get(meta, :line, 1)

    # Extract transition data
    trans = extract_transitions(transitions)

    # Determine all states and initial state
    all_states = collect_states(trans)
    initial = determine_initial_state(trans)

    # Build adjacency graph (from -> [to])
    graph = build_graph(trans, all_states)

    # Run checks
    reachability_errors = check_reachability(all_states, initial, graph, emit?, file, line)
    deadlock_errors = check_deadlock_freedom(all_states, graph, terminal_states, emit?, file, line)
    terminal_errors = check_terminal_states(terminal_states, all_states, file, line)
    hard_errors = check_hard_events(trans, name, file, line)

    coverage_warnings =
      if on_transition_clauses != [] do
        check_on_transition_coverage(trans, on_transition_clauses, name, emit?, file, line)
      else
        []
      end

    all_errors = reachability_errors ++ deadlock_errors ++ terminal_errors ++ hard_errors

    if all_errors == [] do
      if emit? do
        Events.emit(:fsm_verifier, :verification_passed, name, Events.meta(file, line))
      end

      {:ok, [{:verification_passed, name}] ++ coverage_warnings}
    else
      if emit? do
        Events.emit(:fsm_verifier, :verification_failed, all_errors, Events.meta(file, line))
      end

      {:error, all_errors}
    end
  end

  # -- Transition Extraction ---------------------------------------------------

  defp extract_transitions(transition_nodes) do
    Enum.flat_map(transition_nodes, fn
      {:function_call, meta, _} ->
        if Keyword.get(meta, :name) == "transition" do
          from = Keyword.get(meta, :from, "*")
          event = Keyword.get(meta, :event, "")
          to = Keyword.get(meta, :to, "")
          event_kind = Keyword.get(meta, :event_kind, :normal)
          [%{from: from, event: event, to: to, event_kind: event_kind}]
        else
          []
        end

      _ ->
        []
    end)
  end

  # -- State Collection --------------------------------------------------------

  defp collect_states(transitions) do
    froms = Enum.map(transitions, & &1.from) |> Enum.reject(&(&1 == "*"))
    tos = Enum.map(transitions, & &1.to)
    (froms ++ tos) |> Enum.uniq()
  end

  defp determine_initial_state(transitions) do
    # First non-wildcard from state
    case Enum.find(transitions, fn t -> t.from != "*" end) do
      %{from: from} -> from
      nil -> nil
    end
  end

  # -- Graph Building ----------------------------------------------------------

  defp build_graph(transitions, all_states) do
    base = Map.new(all_states, fn s -> {s, []} end)

    Enum.reduce(transitions, base, fn %{from: from, to: to}, graph ->
      if from == "*" do
        # Wildcard: add edge from every state
        Enum.reduce(all_states, graph, fn state, g ->
          Map.update(g, state, [to], fn targets -> [to | targets] end)
        end)
      else
        Map.update(graph, from, [to], fn targets -> [to | targets] end)
      end
    end)
  end

  # -- Reachability (BFS) ------------------------------------------------------

  defp check_reachability(all_states, initial, graph, emit?, file, line) do
    reachable = bfs(initial, graph)

    Enum.flat_map(all_states, fn state ->
      is_reachable = MapSet.member?(reachable, state)

      if emit? do
        Events.emit(
          :fsm_verifier,
          :reachability_result,
          {state, is_reachable},
          Events.meta(file, line)
        )
      end

      if is_reachable do
        []
      else
        [{:unreachable_state, "state '#{state}' is not reachable from initial state '#{initial}'", line: line}]
      end
    end)
  end

  defp bfs(nil, _graph), do: MapSet.new()

  defp bfs(start, graph) do
    do_bfs([start], MapSet.new([start]), graph)
  end

  defp do_bfs([], visited, _graph), do: visited

  defp do_bfs([current | rest], visited, graph) do
    neighbors = Map.get(graph, current, []) |> Enum.uniq()
    new_neighbors = Enum.reject(neighbors, &MapSet.member?(visited, &1))
    new_visited = Enum.reduce(new_neighbors, visited, &MapSet.put(&2, &1))
    do_bfs(rest ++ new_neighbors, new_visited, graph)
  end

  # -- Deadlock Freedom --------------------------------------------------------

  defp check_deadlock_freedom(all_states, graph, terminal_states, emit?, file, line) do
    Enum.flat_map(all_states, fn state ->
      outgoing = Map.get(graph, state, []) |> Enum.uniq()
      has_outgoing = outgoing != []
      is_terminal = state in terminal_states

      if emit? do
        Events.emit(
          :fsm_verifier,
          :deadlock_check,
          {state, has_outgoing or is_terminal},
          Events.meta(file, line)
        )
      end

      if has_outgoing or is_terminal do
        []
      else
        [{:deadlock, "non-terminal state '#{state}' has no outgoing transitions (potential deadlock)", line: line}]
      end
    end)
  end

  # -- Terminal State Validation -----------------------------------------------

  defp check_terminal_states(terminal_states, all_states, _file, line) do
    Enum.flat_map(terminal_states, fn ts ->
      if ts in all_states do
        []
      else
        [{:invalid_terminal, "terminal state '#{ts}' does not exist in the FSM", line: line}]
      end
    end)
  end

  # -- Hard Event Validation ---------------------------------------------------
  # A hard (!) event must be the sole outgoing event from its source state.

  defp check_hard_events(trans, name, _file, line) do
    hard_trans = Enum.filter(trans, &(&1.event_kind == :hard))

    Enum.flat_map(hard_trans, fn %{from: from, event: event} ->
      # Count distinct events leaving this state
      outgoing_events =
        trans
        |> Enum.filter(&(&1.from == from and &1.from != "*"))
        |> Enum.map(& &1.event)
        |> Enum.uniq()

      if length(outgoing_events) > 1 do
        [
          {:hard_event_not_sole,
           "FSM '#{name}': hard event '#{event}!' from state '#{from}' must be the sole outgoing event, but found: #{inspect(outgoing_events)}",
           line: line}
        ]
      else
        []
      end
    end)
  end

  # -- on_transition coverage check --------------------------------------------
  # Warn about (from, event) pairs not explicitly covered by on_transition clauses.
  # This is informational only -- the catch-all clause is expected to handle the rest.

  defp check_on_transition_coverage(trans, _clauses, name, emit?, file, line) do
    # For now, emit an informational event; full clause analysis would require
    # pattern-matching evaluation which is beyond compile-time verification.
    non_wildcard = Enum.reject(trans, &(&1.from == "*"))
    pairs = Enum.map(non_wildcard, fn t -> {t.from, t.event} end) |> Enum.uniq()

    if emit? do
      Events.emit(
        :fsm_verifier,
        :on_transition_coverage,
        {name, length(pairs)},
        Events.meta(file, line)
      )
    end

    # Return informational warnings (not errors) if there are ambiguous transitions
    ambiguous =
      pairs
      |> Enum.group_by(fn {from, _event} -> from end)
      |> Enum.flat_map(fn {from, events_for_state} ->
        events_for_state
        |> Enum.group_by(fn {_from, event} -> event end)
        |> Enum.flat_map(fn {event, _occurrences} ->
          targets = trans |> Enum.filter(&(&1.from == from and &1.event == event)) |> Enum.map(& &1.to)

          if length(targets) > 1 do
            [
              {:ambiguous_transition_warning,
               "FSM '#{name}': event '#{event}' from '#{from}' leads to multiple states #{inspect(targets)}; on_transition must resolve"}
            ]
          else
            []
          end
        end)
      end)

    ambiguous
  end
end
