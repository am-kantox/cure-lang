defmodule Cure.Types.GuardRefinement do
  @moduledoc """
  Guard-based type refinement and coverage analysis.

  Extracts constraints from function guard expressions and uses them to
  refine parameter types within function bodies (flow-sensitive typing).

  ## Guard Constraint Extraction

  Given `fn abs(x: Int) -> Int when x >= 0 = x`, the guard `x >= 0`
  is extracted as a constraint on parameter `x`, refining its type from
  `:int` to `{:refinement, :int, "x", guard_predicate}` inside the body.

  ## Guard Coverage Analysis

  For multi-clause functions with guards, checks whether the guards
  collectively cover all possible input values using SMT solving:

      fn classify(x: Int) -> Atom
        | x when x > 0  -> :positive
        | x when x < 0  -> :negative
        | x when x == 0 -> :zero

  Coverage check: is `not (x > 0 or x < 0 or x == 0)` unsatisfiable?
  If unsat, the guards are exhaustive.
  """

  alias Cure.Types.{Refinement, Env}
  alias Cure.SMT.Solver

  # -- Guard Constraint Extraction ---------------------------------------------

  @doc """
  Extract parameter constraints from a guard AST.

  Returns a map of `%{param_name => guard_predicate_ast}` for each
  parameter that appears in the guard expression.
  """
  @spec extract_constraints(tuple() | nil) :: %{String.t() => tuple()}
  def extract_constraints(nil), do: %{}

  def extract_constraints(guard_ast) do
    vars = collect_guard_variables(guard_ast)

    # For each variable in the guard, the entire guard is its constraint
    # (since guards are typically conjunctions over parameters)
    Map.new(vars, fn var_name -> {var_name, guard_ast} end)
  end

  @doc """
  Refine a typing environment based on guard constraints.

  For each parameter mentioned in the guard, replace its type with
  a refinement type that includes the guard predicate.
  """
  @spec refine_env(Env.t(), tuple() | nil, [{String.t(), atom()}]) :: Env.t()
  def refine_env(env, nil, _params), do: env

  def refine_env(env, guard_ast, params) do
    constraints = extract_constraints(guard_ast)

    Enum.reduce(params, env, fn {param_name, base_type}, e ->
      case Map.get(constraints, param_name) do
        nil ->
          e

        predicate ->
          refined = Refinement.new(base_type, param_name, predicate)
          Env.extend(e, param_name, refined)
      end
    end)
  end

  # -- Guard Coverage Analysis -------------------------------------------------

  @doc """
  Check if a set of guard clauses covers all possible values for a type.

  Takes a list of guard ASTs and the parameter types. Uses SMT to check
  if the disjunction of all guards is a tautology (always true).

  Returns `:exhaustive`, `{:non_exhaustive, description}`, or `:unknown`.
  """
  @spec check_guard_coverage([tuple() | nil], String.t(), atom()) ::
          :exhaustive | {:non_exhaustive, String.t()} | :unknown
  def check_guard_coverage(guard_asts, var_name, base_type) do
    # Filter out nil guards (clauses without when)
    non_nil_guards = Enum.filter(guard_asts, &(&1 != nil))

    cond do
      # If any clause has no guard, it catches everything
      length(non_nil_guards) < length(guard_asts) ->
        :exhaustive

      non_nil_guards == [] ->
        :exhaustive

      true ->
        check_with_smt(non_nil_guards, var_name, base_type)
    end
  end

  @doc """
  Detect unreachable clauses in a multi-clause function.

  A clause is unreachable if its guard is implied by the disjunction
  of all previous guards (meaning all its inputs are already handled).

  Returns a list of 0-based indices of unreachable clauses.
  """
  @spec find_unreachable_clauses([tuple() | nil], String.t(), atom()) :: [non_neg_integer()]
  def find_unreachable_clauses(guard_asts, var_name, base_type) do
    if not Solver.available?() do
      []
    else
      {_, unreachable} =
        Enum.reduce(Enum.with_index(guard_asts), {[], []}, fn {guard, idx}, {prev_guards, unreachable} ->
          case guard do
            nil ->
              # No guard -- always reachable (catches remaining)
              {prev_guards ++ [guard], unreachable}

            _ ->
              if prev_guards_cover?(prev_guards, guard, var_name, base_type) do
                {prev_guards ++ [guard], [idx | unreachable]}
              else
                {prev_guards ++ [guard], unreachable}
              end
          end
        end)

      Enum.reverse(unreachable)
    end
  end

  # -- Internal ----------------------------------------------------------------

  defp collect_guard_variables(ast) do
    ast
    |> do_collect_vars([])
    |> Enum.uniq()
  end

  defp do_collect_vars({:variable, _, name}, acc) when name != "_", do: [name | acc]

  defp do_collect_vars({:binary_op, _, [left, right]}, acc) do
    acc = do_collect_vars(left, acc)
    do_collect_vars(right, acc)
  end

  defp do_collect_vars({:unary_op, _, [operand]}, acc) do
    do_collect_vars(operand, acc)
  end

  defp do_collect_vars({:function_call, _, args}, acc) do
    Enum.reduce(args, acc, &do_collect_vars/2)
  end

  defp do_collect_vars(_ast, acc), do: acc

  defp check_with_smt(guards, var_name, base_type) do
    if not Solver.available?() do
      :unknown
    else
      # Build disjunction of all guards: G1 or G2 or ... or Gn
      disjunction = build_disjunction(guards)

      # Check if NOT(disjunction) is unsatisfiable
      # If unsat, the disjunction is a tautology => guards are exhaustive
      negated = {:unary_op, [operator: :not, category: :boolean], [disjunction]}

      case Solver.check_sat(negated, %{var_name => base_type}) do
        :unsat -> :exhaustive
        :sat -> {:non_exhaustive, "guards do not cover all cases for #{var_name}"}
        :unknown -> :unknown
      end
    end
  end

  defp prev_guards_cover?([], _current, _var, _type), do: false

  defp prev_guards_cover?(prev_guards, current_guard, var_name, base_type) do
    # A clause is unreachable if every value that satisfies its guard
    # also satisfies some previous guard. In BEAM, first match wins.
    # Check: current_guard => (prev1 or prev2 or ...)
    prev_non_nil = Enum.filter(prev_guards, &(&1 != nil))

    if prev_non_nil == [] do
      false
    else
      prev_disj = build_disjunction(prev_non_nil)
      Solver.prove_implication(current_guard, prev_disj, var_name, base_type) == true
    end
  end

  defp build_disjunction([single]), do: single

  defp build_disjunction([head | tail]) do
    rest = build_disjunction(tail)
    {:binary_op, [operator: :or, category: :boolean], [head, rest]}
  end
end
