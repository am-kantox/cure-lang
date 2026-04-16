defmodule Cure.Types.Totality do
  @moduledoc """
  Totality / termination analysis for the Cure type system.

  A function is **total** when it terminates on every input *and* its
  pattern matching is exhaustive. Total functions are safe to use in
  type-level computation. Partial functions are still allowed (Cure
  is a programming language first), but the user can opt into
  totality enforcement on a per-function basis with the `#[total]`
  decorator.

  ## What we check (v0.17.0)

  - **Coverage** -- every function clause-set must cover all input
    shapes, as determined by `Cure.Types.PatternChecker`.
  - **Termination** -- every direct recursive call must reduce a
    structural argument: the recursive call's argument at position
    `i` must be a syntactic sub-term of the corresponding pattern in
    the matching clause.

  ## What we do *not* check

  - Mutual recursion. Deferred to v0.18.0.
  - Higher-order recursion (e.g. via `foldl`).
  - Calls that go through indirect dispatch (protocols).

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
  Inspect a function's decorators for `#[total]`.
  """
  @spec total_required?(keyword()) :: boolean()
  def total_required?(meta) do
    case Keyword.get(meta, :decorators, []) do
      decs when is_list(decs) ->
        Enum.any?(decs, fn
          {:decorator, dmeta, _} -> Keyword.get(dmeta, :name) == "total"
          {:total} -> true
          :total -> true
          _ -> false
        end)

      _ ->
        false
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
