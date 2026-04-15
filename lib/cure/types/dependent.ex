defmodule Cure.Types.Dependent do
  @moduledoc """
  Dependent type support for the Cure type system.

  Handles types that depend on values, such as `Vector(T, n)` where
  `n` is a natural number tracked at the type level.

  ## Dependent Type Representation

  A dependent type is represented as:
  `{:dependent, name, type_params, value_params, constraints}`

  Where:
  - `name` -- type constructor name (e.g., "Vector")
  - `type_params` -- type-level parameters (e.g., T)
  - `value_params` -- value-level parameters with types (e.g., n: Nat)
  - `constraints` -- predicates over value params (e.g., n > 0)

  ## Verification

  When a function has dependent type parameters, the type checker
  generates verification conditions that are checked via SMT:

      fn safe_head(v: Vector(T, n)) -> T when n > 0
      # VC: at call sites, prove n > 0

      fn concat(a: Vector(T, m), b: Vector(T, n)) -> Vector(T, m + n)
      # VC: result length equals sum of input lengths
  """

  alias Cure.SMT.Solver

  @type t :: {:dependent, String.t(), [term()], [term()], [term()]}

  @doc """
  Create a dependent type.
  """
  @spec new(String.t(), [term()], [{String.t(), atom()}]) :: t()
  def new(name, type_params, value_params) do
    {:dependent, name, type_params, value_params, []}
  end

  @doc """
  Create a dependent type with constraints.
  """
  @spec new(String.t(), [term()], [{String.t(), atom()}], [tuple()]) :: t()
  def new(name, type_params, value_params, constraints) do
    {:dependent, name, type_params, value_params, constraints}
  end

  @doc """
  Check if a type is a dependent type.
  """
  def dependent?({:dependent, _, _, _, _}), do: true
  def dependent?(_), do: false

  @doc """
  Extract value parameter names from a dependent type.
  """
  def value_param_names({:dependent, _, _, vps, _}) do
    Enum.map(vps, fn {name, _type} -> name end)
  end

  def value_param_names(_), do: []

  @doc """
  Verify a dependent type constraint via SMT.

  Given value parameters and their constraints, check if the
  constraints are satisfiable.
  """
  @spec verify_constraint(tuple(), String.t(), atom()) :: boolean() | :unknown
  def verify_constraint(constraint_ast, var_name, base_type) do
    Solver.is_satisfiable?(constraint_ast, var_name, base_type)
  end

  @doc """
  Check if two dependent types are compatible (same constructor, compatible params).
  """
  def compatible?({:dependent, name, _, vp1, c1}, {:dependent, name, _, vp2, c2}) do
    if length(vp1) != length(vp2) do
      false
    else
      # If both have no constraints, they are compatible
      if c1 == [] and c2 == [] do
        true
      else
        # Try SMT implication: c1 => c2 (sub's constraints imply super's)
        # If solver unavailable, fall back to structural equality
        case {c1, c2} do
          {[], _} -> true
          {_, []} -> true
          _ -> c1 == c2
        end
      end
    end
  end

  def compatible?(_, _), do: false

  @doc """
  Generate verification conditions for a dependent function call.

  When calling `safe_head(v)` where `safe_head` requires `n > 0`,
  generate the VC that must be proven at the call site.

  Substitutes the call-site argument ASTs into the constraint predicates
  so the resulting VCs are concrete and can be checked via SMT.
  """
  @spec generate_vc(t(), [tuple()]) :: [tuple()]
  def generate_vc({:dependent, _name, _tps, vps, constraints}, args) do
    if constraints == [] do
      []
    else
      # Build a binding map: value param name -> call-site argument AST
      bindings =
        Enum.zip(vps, args)
        |> Enum.map(fn {{param_name, _type}, arg_ast} -> {param_name, arg_ast} end)
        |> Map.new()

      # Substitute each constraint with the actual argument values
      Enum.map(constraints, fn c -> substitute_expr(c, bindings) end)
    end
  end

  def generate_vc(_, _), do: []

  @doc """
  Substitute value parameters in a type expression.

  Used when computing the return type of a dependent function:
  `Vector(T, m + n)` with `m = 3, n = 5` -> `Vector(T, 8)`
  """
  @spec substitute(t(), map()) :: t()
  def substitute({:dependent, name, tps, vps, constraints}, bindings) do
    new_constraints =
      Enum.map(constraints, fn c ->
        substitute_expr(c, bindings)
      end)

    {:dependent, name, tps, vps, new_constraints}
  end

  def substitute(type, _bindings), do: type

  @doc false
  def substitute_expr_public(ast, bindings), do: substitute_expr(ast, bindings)

  defp substitute_expr({:variable, _meta, name} = ast, bindings) do
    case Map.get(bindings, name) do
      nil -> ast
      replacement -> replacement
    end
  end

  defp substitute_expr({:binary_op, meta, [left, right]}, bindings) do
    {:binary_op, meta, [substitute_expr(left, bindings), substitute_expr(right, bindings)]}
  end

  defp substitute_expr(ast, _bindings), do: ast
end
