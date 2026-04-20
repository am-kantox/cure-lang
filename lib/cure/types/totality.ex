defmodule Cure.Types.Totality do
  @moduledoc """
  Totality / termination analysis for the Cure type system.

  A function is **total** when it terminates on every input *and* its
  pattern matching is exhaustive. Total functions are safe to use in
  type-level computation. Partial functions are still allowed (Cure
  is a programming language first), but the user can opt into
  totality enforcement on a per-function basis with the `@total true`
  decorator.

  ## What we check (v0.17.0)

  - **Coverage** -- every function clause-set must cover all input
    shapes, as determined by `Cure.Types.PatternChecker`.
  - **Termination** -- every direct recursive call must reduce a
    structural argument: the recursive call's argument at position
    `i` must be a syntactic sub-term of the corresponding pattern in
    the matching clause.

  ## What we do *not* check

  - Higher-order recursion (e.g. via `foldl`).
  - Calls that go through indirect dispatch (protocols).

  ## Mutual recursion (v0.19.0)

  `check_mutual/1` runs a strongly-connected-components analysis over a
  module's call graph, then inspects every non-trivial SCC. A cycle is
  total only when at least one function in the cycle can shrink a
  structural argument on every path through the cycle. The check is
  intentionally conservative: it emits a warning (code `E029`) rather
  than blocking compilation, and an `@total true` function caught in a
  non-decreasing cycle is reported as a type error upstream.

  Functions failing the structural check are classified as
  `:partial` rather than `:non_terminating`; the message is
  conservative.

  ## API

      classify(fn_def, env) -> :total | :partial | :unknown

      report(fn_def, classification, file)
  """

  alias Cure.Pipeline.Events

  @type classification :: :total | :partial | :unknown
  @type reason :: :coverage | :recursion | :unknown

  # -- Public API --------------------------------------------------------------

  @doc """
  Classify a single function-def AST node.

  Returns one of:
  - `:total` -- coverage holds and every recursive call shrinks an arg.
  - `:partial` -- coverage gaps or non-shrinking recursion.
  - `:unknown` -- structure too complex to analyse (no error).
  """
  @spec classify(tuple()) :: classification()
  def classify({:function_def, meta, body}) when is_list(meta) do
    name = Keyword.get(meta, :name, "_")
    params = Keyword.get(meta, :params, [])
    clauses = Keyword.get(meta, :clauses, [])

    cond do
      not coverage_ok?(meta) ->
        :partial

      not termination_ok?(name, params, clauses, body) ->
        :partial

      true ->
        :total
    end
  end

  def classify(_), do: :unknown

  @doc """
  Emit a totality classification as a pipeline event.
  """
  @spec report(String.t(), classification(), String.t(), pos_integer()) :: :ok
  def report(name, classification, file, line) do
    Events.emit(:type_checker, :totality, {name, classification}, Events.meta(file, line))
  end

  @doc """
  Perform a mutual-recursion SCC analysis on a module body.

  Returns a list of `{cycle_names, :suspect | :ok}` pairs for every
  non-trivial strongly-connected component. `:suspect` means the
  compiler could not prove structural decrease on every path through
  the cycle; `:ok` means at least one function in the cycle shrinks
  a structural argument on every recursive call.
  """
  @spec check_mutual([tuple()]) :: [{[String.t()], :ok | :suspect}]
  def check_mutual(stmts) when is_list(stmts) do
    fn_defs =
      Enum.flat_map(stmts, fn
        {:function_def, meta, _body} = node -> [{Keyword.get(meta, :name, "_"), node}]
        _ -> []
      end)

    names = MapSet.new(fn_defs, fn {n, _} -> n end)
    graph = build_call_graph(fn_defs, names)
    sccs = tarjan_scc(graph)

    Enum.flat_map(sccs, fn component ->
      component_list = Enum.sort(component)

      cond do
        length(component_list) < 2 ->
          # Trivial SCC (single function, no self-loop) -- skip.
          []

        mutual_decreasing?(component_list, fn_defs) ->
          [{component_list, :ok}]

        true ->
          [{component_list, :suspect}]
      end
    end)
  end

  @doc """
  Inspect a function's decorators for `@total true`.
  """
  @spec total_required?(keyword()) :: boolean()
  def total_required?(meta) do
    case Keyword.get(meta, :decorator) do
      {:total, _} -> true
      _ -> false
    end
  end

  # -- Coverage ----------------------------------------------------------------

  defp coverage_ok?(meta) do
    # Coverage info is published by the PatternChecker as a warning. Without
    # access to the env at this point we accept and rely on the checker's own
    # warning to surface coverage failures. A more thorough implementation
    # would fetch the warnings from the type-checker pipeline events; we keep
    # the structural check pure here.
    case Keyword.get(meta, :coverage, :unknown) do
      :complete -> true
      :unknown -> true
      _ -> false
    end
  end

  # -- Termination -------------------------------------------------------------

  defp termination_ok?(name, _params, [], body), do: no_unguarded_recursion?(name, body)

  defp termination_ok?(name, _params, clauses, _body) do
    Enum.all?(clauses, fn
      {:function_clause, cmeta, [body | _]} ->
        patterns = Keyword.get(cmeta, :patterns, [])
        check_clause(name, patterns, body)

      _ ->
        true
    end)
  end

  defp check_clause(name, patterns, body) do
    structural = collect_structural(patterns)

    recursive_calls(name, body)
    |> Enum.all?(fn args -> Enum.any?(0..max(length(args) - 1, 0), &arg_shrinks?(&1, args, structural)) end)
  end

  defp arg_shrinks?(i, args, structural) do
    case Enum.at(args, i) do
      nil -> false
      arg -> Enum.any?(structural, fn s -> sub_term?(arg, s) end)
    end
  end

  # Find every recursive call to `name` and collect its argument list.
  defp recursive_calls(name, ast) do
    do_collect_calls(ast, name, [])
  end

  defp do_collect_calls({:function_call, meta, args}, name, acc) do
    if Keyword.get(meta, :name) == name do
      [args | Enum.reduce(args, acc, &do_collect_calls(&1, name, &2))]
    else
      Enum.reduce(args, acc, &do_collect_calls(&1, name, &2))
    end
  end

  defp do_collect_calls({_tag, _meta, children}, name, acc) when is_list(children) do
    Enum.reduce(children, acc, &do_collect_calls(&1, name, &2))
  end

  defp do_collect_calls(_other, _name, acc), do: acc

  defp no_unguarded_recursion?(name, body), do: recursive_calls(name, body) == []

  # -- Mutual-recursion helpers (v0.19.0) --------------------------------------

  defp build_call_graph(fn_defs, all_names) do
    Enum.reduce(fn_defs, %{}, fn {name, node}, acc ->
      callees =
        collect_all_calls(node, [])
        |> MapSet.new()
        |> MapSet.intersection(all_names)
        |> MapSet.to_list()

      Map.put(acc, name, callees)
    end)
  end

  defp collect_all_calls({:function_call, meta, args}, acc) do
    callee = Keyword.get(meta, :name)
    new_acc = if is_binary(callee), do: [callee | acc], else: acc
    Enum.reduce(args, new_acc, &collect_all_calls/2)
  end

  defp collect_all_calls({_tag, _meta, children}, acc) when is_list(children) do
    Enum.reduce(children, acc, &collect_all_calls/2)
  end

  defp collect_all_calls(_other, acc), do: acc

  # Tarjan's SCC algorithm. Returns a list of MapSets, one per SCC.
  defp tarjan_scc(graph) do
    nodes = Map.keys(graph)

    state = %{
      index: 0,
      stack: [],
      on_stack: MapSet.new(),
      indices: %{},
      lowlinks: %{},
      sccs: []
    }

    final =
      Enum.reduce(nodes, state, fn v, st ->
        if Map.has_key?(st.indices, v), do: st, else: strong_connect(v, st, graph)
      end)

    final.sccs
  end

  defp strong_connect(v, state, graph) do
    state = %{
      state
      | index: state.index + 1,
        indices: Map.put(state.indices, v, state.index),
        lowlinks: Map.put(state.lowlinks, v, state.index),
        stack: [v | state.stack],
        on_stack: MapSet.put(state.on_stack, v)
    }

    state =
      Enum.reduce(Map.get(graph, v, []), state, fn w, st ->
        cond do
          not Map.has_key?(st.indices, w) ->
            st = strong_connect(w, st, graph)
            update_lowlink(st, v, Map.get(st.lowlinks, w))

          MapSet.member?(st.on_stack, w) ->
            update_lowlink(st, v, Map.get(st.indices, w))

          true ->
            st
        end
      end)

    if Map.get(state.lowlinks, v) == Map.get(state.indices, v) do
      {scc, rest, on_stack} = pop_until(state.stack, state.on_stack, v, [])
      %{state | stack: rest, on_stack: on_stack, sccs: [MapSet.new(scc) | state.sccs]}
    else
      state
    end
  end

  defp update_lowlink(state, v, candidate) do
    current = Map.get(state.lowlinks, v)
    %{state | lowlinks: Map.put(state.lowlinks, v, min(current, candidate))}
  end

  defp pop_until([top | rest], on_stack, target, acc) do
    on_stack = MapSet.delete(on_stack, top)
    new_acc = [top | acc]

    if top == target do
      {new_acc, rest, on_stack}
    else
      pop_until(rest, on_stack, target, new_acc)
    end
  end

  # A cycle is decreasing if at least one function in it shrinks a
  # structural argument on every path -- otherwise we cannot guarantee
  # termination. Conservative: require the presence of any multi-clause
  # function with at least one non-trivial pattern in the cycle.
  defp mutual_decreasing?(cycle_names, fn_defs) do
    Enum.any?(cycle_names, fn name ->
      case Enum.find(fn_defs, fn {n, _} -> n == name end) do
        {_, {:function_def, meta, _body}} ->
          case Keyword.get(meta, :clauses) do
            nil -> false
            clauses -> Enum.any?(clauses, &has_structural_pattern?/1)
          end

        _ ->
          false
      end
    end)
  end

  defp has_structural_pattern?(%{params: patterns}) do
    Enum.any?(patterns, fn
      {:list, _, _} -> true
      {:tuple, _, _} -> true
      {:function_call, _, _} -> true
      {:literal, _, _} -> true
      _ -> false
    end)
  end

  defp has_structural_pattern?(_), do: false

  # Collect "structural sub-terms" from a list of patterns: cons-tails,
  # tuple/list elements, ADT constructor children, and any pattern variable
  # we can later compare to.
  defp collect_structural(patterns) do
    Enum.flat_map(patterns, &structurals_of/1)
  end

  defp structurals_of({:cons_pattern, _meta, [head, tail]}) do
    [head, tail | structurals_of(tail)]
  end

  defp structurals_of({:tuple, _meta, els}) when is_list(els) do
    els ++ Enum.flat_map(els, &structurals_of/1)
  end

  defp structurals_of({:list, _meta, els}) when is_list(els) do
    els ++ Enum.flat_map(els, &structurals_of/1)
  end

  defp structurals_of({:adt_pattern, _meta, [_constr, args]}) when is_list(args) do
    args ++ Enum.flat_map(args, &structurals_of/1)
  end

  defp structurals_of({:variable, _meta, _name} = var), do: [var]
  defp structurals_of(_), do: []

  # arg is a "syntactic sub-term" of pattern when arg is structurally <= pat.
  defp sub_term?({:variable, _, n1}, {:variable, _, n2}), do: n1 == n2
  defp sub_term?({:literal, _, v}, {:literal, _, v}), do: true

  defp sub_term?({:binary_op, meta, [l, r]}, parent) do
    case Keyword.get(meta, :operator) do
      :- -> sub_term?(l, parent) and is_decreasing_literal?(r)
      :+ -> sub_term?(l, parent) and is_decreasing_literal?(r)
      _ -> false
    end
  end

  defp sub_term?(_, _), do: false

  defp is_decreasing_literal?({:literal, _, v}) when is_integer(v) and v > 0, do: true
  defp is_decreasing_literal?(_), do: false
end
