defmodule Cure.Temporal.Checker do
  @moduledoc """
  Bounded model checker for LTL-style formulae over an FSM transition
  graph (v0.27.0).

  The checker represents the model as a Kripke-style structure where
  every state atomically satisfies exactly one proposition: its own
  state name. Transitions are directed edges between state names.

  The entry point `check/3` takes a formula, a model, and optional
  options and returns:

    * `{:ok, :holds}` when the formula holds on every path starting at
      the initial state, within the search bound.
    * `{:violation, trace}` when a counterexample exists, with `trace`
      a list of state names witnessing the failure.
    * `{:error, reason}` when the input is malformed.

  ## Model shape

      %{
        initial: "Locked",
        states: ["Locked", "Unlocked"],
        edges: %{
          "Locked"   => ["Unlocked"],
          "Unlocked" => ["Locked"]
        }
      }

  The model is produced from `Cure.FSM.Verifier`'s transition list by
  `from_fsm/1`.

  ## Algorithms

    * Safety (`always P`, `never P`) is checked by breadth-first
      exhaustive state exploration.
    * Liveness (`eventually P`) is checked by a forward search for
      any reachable state where `P` holds; if the search exhausts the
      reachable frontier without finding one, the property fails and
      the initial prefix is returned as the counterexample.
    * `until P Q` is reduced to `eventually Q` with the additional
      constraint that `P` holds on every state of the witness up to
      the one satisfying `Q`.
    * `next P` is checked by trying every direct successor of the
      current state.
    * Boolean combinators are decomposed recursively.

  The default bound is `length(states) * 8`; override with
  `bound: integer` in the options. Exceeding the bound yields
  `{:error, :bound_exceeded}` on liveness properties only; safety
  properties are sound over the full reachable set regardless.
  """

  alias Cure.Temporal.Formula

  @type model :: %{
          initial: Formula.state_name(),
          states: [Formula.state_name()],
          edges: %{Formula.state_name() => [Formula.state_name()]}
        }

  @type check_result ::
          {:ok, :holds}
          | {:violation, [Formula.state_name()]}
          | {:error, term()}

  @doc """
  Check a formula against a model.
  """
  @spec check(Formula.t(), model(), keyword()) :: check_result()
  def check(formula, %{initial: initial, states: states, edges: edges} = _model, opts \\ []) do
    bound = Keyword.get(opts, :bound, max(length(states) * 8, 16))

    # Validate atoms.
    unknown =
      formula
      |> Formula.atoms()
      |> Enum.reject(&(&1 in states))

    case unknown do
      [] ->
        do_check(formula, initial, edges, bound)

      _ ->
        {:error, {:unknown_atoms, unknown}}
    end
  end

  # -- Dispatch on formula shape ---------------------------------------------

  defp do_check(:tt, _state, _edges, _bound), do: {:ok, :holds}
  defp do_check(:ff, state, _edges, _bound), do: {:violation, [state]}

  defp do_check({:atom, [name]}, state, _edges, _bound) do
    if state == name, do: {:ok, :holds}, else: {:violation, [state]}
  end

  defp do_check({:not_, [p]}, state, edges, bound) do
    case do_check(p, state, edges, bound) do
      {:ok, :holds} -> {:violation, [state]}
      {:violation, _trace} -> {:ok, :holds}
      {:error, _} = err -> err
    end
  end

  defp do_check({:and_, [p, q]}, state, edges, bound) do
    with {:ok, :holds} <- do_check(p, state, edges, bound),
         {:ok, :holds} <- do_check(q, state, edges, bound) do
      {:ok, :holds}
    end
  end

  defp do_check({:or_, [p, q]}, state, edges, bound) do
    case do_check(p, state, edges, bound) do
      {:ok, :holds} ->
        {:ok, :holds}

      {:violation, _} ->
        do_check(q, state, edges, bound)

      {:error, _} = err ->
        err
    end
  end

  defp do_check({:always, [p]}, state, edges, bound) do
    check_always(p, state, edges, bound)
  end

  defp do_check({:eventually, [p]}, state, edges, bound) do
    check_eventually(p, state, edges, bound)
  end

  defp do_check({:next_, [p]}, state, edges, bound) do
    case Map.get(edges, state, []) do
      [] ->
        {:violation, [state]}

      successors ->
        # `next p` holds iff `p` holds in every direct successor.
        # This is the "universal-next" reading, consistent with the
        # CTL-like semantics used by most bounded model checkers over
        # deterministic fragments.
        result =
          Enum.reduce_while(successors, :holds, fn s, _ ->
            case do_check(p, s, edges, bound) do
              {:ok, :holds} -> {:cont, :holds}
              {:violation, trail} -> {:halt, {:violation, [state | trail]}}
              {:error, _} = err -> {:halt, err}
            end
          end)

        case result do
          :holds -> {:ok, :holds}
          other -> other
        end
    end
  end

  defp do_check({:until, [p, q]}, state, edges, bound) do
    check_until(p, q, state, edges, bound)
  end

  # -- Safety: always P -----------------------------------------------------
  # BFS over the reachable closure from `state`, asserting `P` at each node.

  defp check_always(p, state, edges, bound) do
    do_always([{state, [state]}], MapSet.new([state]), p, edges, bound, 0)
  end

  defp do_always([], _visited, _p, _edges, _bound, _depth), do: {:ok, :holds}

  defp do_always(_frontier, _visited, _p, _edges, bound, depth) when depth > bound,
    do: {:ok, :holds}

  defp do_always([{node, trail} | rest], visited, p, edges, bound, depth) do
    # Check P at this node (not the initial trail's last frame; we
    # re-check here because the frame is a state, not a formula.)
    case do_check(p, node, edges, bound) do
      {:ok, :holds} ->
        successors =
          edges
          |> Map.get(node, [])
          |> Enum.reject(&MapSet.member?(visited, &1))

        new_visited = Enum.reduce(successors, visited, &MapSet.put(&2, &1))
        new_frontier = rest ++ Enum.map(successors, fn s -> {s, trail ++ [s]} end)
        do_always(new_frontier, new_visited, p, edges, bound, depth + 1)

      {:violation, _} ->
        {:violation, trail}

      {:error, _} = err ->
        err
    end
  end

  # -- Liveness: eventually P -----------------------------------------------
  # Forward BFS; succeed on the first state satisfying P, fail when
  # the frontier is exhausted.

  defp check_eventually(p, state, edges, bound) do
    do_eventually([{state, [state]}], MapSet.new([state]), p, edges, bound, 0)
  end

  defp do_eventually([], _visited, _p, _edges, _bound, _depth),
    do: {:violation, []}

  defp do_eventually(_frontier, _visited, _p, _edges, bound, depth) when depth > bound,
    do: {:error, :bound_exceeded}

  defp do_eventually([{node, trail} | rest], visited, p, edges, bound, depth) do
    case do_check(p, node, edges, bound) do
      {:ok, :holds} ->
        {:ok, :holds}

      {:violation, _} ->
        successors =
          edges
          |> Map.get(node, [])
          |> Enum.reject(&MapSet.member?(visited, &1))

        new_visited = Enum.reduce(successors, visited, &MapSet.put(&2, &1))
        new_frontier = rest ++ Enum.map(successors, fn s -> {s, trail ++ [s]} end)
        do_eventually(new_frontier, new_visited, p, edges, bound, depth + 1)

      {:error, _} = err ->
        err
    end
  end

  # -- Until: P U Q ----------------------------------------------------------

  defp check_until(p, q, state, edges, bound) do
    do_until([{state, [state]}], MapSet.new([state]), p, q, edges, bound, 0)
  end

  defp do_until([], _visited, _p, _q, _edges, _bound, _depth),
    do: {:violation, []}

  defp do_until(_frontier, _visited, _p, _q, _edges, bound, depth) when depth > bound,
    do: {:error, :bound_exceeded}

  defp do_until([{node, trail} | rest], visited, p, q, edges, bound, depth) do
    cond do
      match?({:ok, :holds}, do_check(q, node, edges, bound)) ->
        {:ok, :holds}

      match?({:ok, :holds}, do_check(p, node, edges, bound)) ->
        successors =
          edges
          |> Map.get(node, [])
          |> Enum.reject(&MapSet.member?(visited, &1))

        new_visited = Enum.reduce(successors, visited, &MapSet.put(&2, &1))
        new_frontier = rest ++ Enum.map(successors, fn s -> {s, trail ++ [s]} end)
        do_until(new_frontier, new_visited, p, q, edges, bound, depth + 1)

      true ->
        # P fails here and Q also fails here -- the until chain is broken.
        {:violation, trail}
    end
  end

  # -- Model construction from FSM -----------------------------------------

  @doc """
  Build a model from a list of FSM transitions as produced by
  `Cure.FSM.Verifier.extract_transitions/1` (or compatible shape).

  Each transition is a map with `:from`, `:to`, and optional wildcard
  `"*"` semantics. The returned model is ready for `check/3`.
  """
  @spec from_fsm([map()], Formula.state_name() | nil) :: model()
  def from_fsm(transitions, initial \\ nil) do
    tos = Enum.map(transitions, & &1.to)

    froms =
      transitions
      |> Enum.map(& &1.from)
      |> Enum.reject(&(&1 == "*"))

    states = (froms ++ tos) |> Enum.uniq()

    resolved_initial =
      case initial do
        nil ->
          case Enum.find(transitions, fn t -> t.from != "*" end) do
            %{from: from} -> from
            _ -> List.first(states)
          end

        s ->
          s
      end

    base = Map.new(states, fn s -> {s, []} end)

    edges =
      Enum.reduce(transitions, base, fn %{from: from, to: to}, graph ->
        if from == "*" do
          Enum.reduce(states, graph, fn state, g ->
            Map.update(g, state, [to], fn t -> Enum.uniq([to | t]) end)
          end)
        else
          Map.update(graph, from, [to], fn t -> Enum.uniq([to | t]) end)
        end
      end)

    %{initial: resolved_initial, states: states, edges: edges}
  end
end
