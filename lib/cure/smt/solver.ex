defmodule Cure.SMT.Solver do
  @moduledoc """
  High-level SMT constraint checking API for the Cure type system.

  Provides:
  - Constraint satisfiability checking
  - Implication proving (for refinement subtyping)
  - Refinement subtype verification

  Falls back to a conservative symbolic evaluator when Z3 is not available.

  ## Usage

      # Check if a constraint is satisfiable
      {:sat, _} = Cure.SMT.Solver.check_sat(predicate_ast)

      # Prove refinement subtyping: {x: Int | x > 0} <: {x: Int | x != 0}
      true = Cure.SMT.Solver.prove_subtype(pred1, pred2, "x", :int)
  """

  alias Cure.SMT.{Process, Translator}

  @doc """
  Check if a constraint AST is satisfiable.

  Returns `:sat`, `:unsat`, or `:unknown`.
  """
  @spec check_sat(tuple(), map()) :: :sat | :unsat | :unknown
  def check_sat(constraint_ast, var_types \\ %{}) do
    query = Translator.generate_query(constraint_ast, var_types)
    run_query(query)
  end

  @doc """
  Prove that `pred1` implies `pred2` (for refinement subtyping).

  To prove `forall x. P1(x) => P2(x)`, we check if `P1(x) and not P2(x)`
  is unsatisfiable. Returns `true` (proven), `false` (counterexample exists),
  or `:unknown`.
  """
  @spec prove_implication(tuple(), tuple(), String.t(), atom()) :: boolean() | :unknown
  def prove_implication(pred1, pred2, var_name, base_type) do
    query = Translator.generate_subtype_query(pred1, pred2, var_name, base_type)

    case run_query(query) do
      :unsat -> true
      :sat -> false
      :unknown -> :unknown
    end
  end

  @doc """
  Check if a refinement subtype relationship holds.

  `{x: T | P1(x)} <: {x: T | P2(x)}` iff `forall x. P1(x) => P2(x)`.
  """
  @spec check_refinement_subtype(tuple(), tuple(), String.t(), atom()) :: boolean() | :unknown
  def check_refinement_subtype(sub_pred, super_pred, var_name, base_type) do
    prove_implication(sub_pred, super_pred, var_name, base_type)
  end

  @doc """
  Verify that a constraint is satisfiable (has at least one solution).

  Useful for checking that refinement type definitions are not empty.
  """
  @spec is_satisfiable?(tuple(), String.t(), atom()) :: boolean()
  def is_satisfiable?(predicate, var_name, base_type) do
    query = Translator.generate_constraint_query(predicate, var_name, base_type)
    run_query(query) == :sat
  end

  @doc """
  Prove an implication and return a counterexample if it fails.

  Returns `{:proven, nil}`, `{:failed, model}`, or `{:unknown, nil}`.
  """
  @spec prove_with_counterexample(tuple(), tuple(), String.t(), atom()) ::
          {:proven, nil} | {:failed, map()} | {:unknown, nil}
  def prove_with_counterexample(pred1, pred2, var_name, base_type) do
    smt_type =
      case base_type do
        :int -> "Int"
        :float -> "Real"
        _ -> "Int"
      end

    query =
      "(set-logic QF_LIA)\n" <>
        "(declare-const #{var_name} #{smt_type})\n" <>
        "(assert (and #{Translator.translate(pred1)} (not #{Translator.translate(pred2)})))\n" <>
        "(check-sat)\n" <>
        "(get-model)\n"

    case run_query_raw(query) do
      {:unsat, _} ->
        {:proven, nil}

      {:sat, output} ->
        case Cure.SMT.Parser.parse_model(output) do
          {:ok, model} -> {:failed, model}
          _ -> {:failed, %{}}
        end

      _ ->
        {:unknown, nil}
    end
  end

  @doc """
  Check if Z3 is available for SMT solving.
  """
  @spec available?() :: boolean()
  def available?, do: Process.z3_available?()

  # -- Internal ----------------------------------------------------------------

  defp run_query(query) do
    if Process.z3_available?() do
      run_with_z3(query)
    else
      # Conservative fallback: we cannot prove anything without Z3
      :unknown
    end
  end

  defp run_with_z3(query) do
    case Process.start_link(timeout: 3_000) do
      {:ok, pid} ->
        try do
          result = Process.query(pid, query)

          case result do
            {:sat, _} -> :sat
            {:unsat, _} -> :unsat
            {:unknown, _} -> :unknown
            {:error, _} -> :unknown
          end
        after
          Process.stop(pid)
        end

      {:error, _} ->
        :unknown
    end
  end

  defp run_query_raw(query) do
    if Process.z3_available?() do
      case Process.start_link(timeout: 3_000) do
        {:ok, pid} ->
          try do
            Process.query(pid, query)
          after
            Process.stop(pid)
          end

        {:error, _} ->
          {:unknown, ""}
      end
    else
      {:unknown, ""}
    end
  end
end
