defmodule Cure.Types.PathRefinement do
  @moduledoc """
  Path-sensitive refinement flow analysis.

  When the type checker descends into the `then` and `else` branches
  of a conditional, it learns information about variables that *must*
  be true (or false) along that path. This module turns that
  information into a refined type for any variable referenced in the
  guarding expression.

  Today this hooks the bidirectional checker at:

  - `if cond then a else b` -- in `a` the assumption `cond = true`
    holds; in `b` the assumption `cond = false` holds.
  - `match v with | pat when guard -> body` -- in `body` the guard
    is known to hold.

  ## Refinement extraction

  We support a deliberately simple language of guards:

  - `x == c`, `x != c`, `x < c`, `x <= c`, `x > c`, `x >= c`
    where `x` is a variable and `c` is a literal.
  - `is_int(x)`, `is_float(x)`, `is_string(x)` -- type predicates.
  - `not (...)`, `(...) and (...)`, `(...) or (...)` -- composition.

  Anything outside this fragment is *ignored* for refinement
  purposes, leaving the variable's type unchanged.

  ## Output

  `refine_along/3` returns a map `%{var_name => refined_type}` of
  refinements that hold along the supplied truth-direction.
  """

  alias Cure.Types.Refinement

  @type direction :: :true_branch | :false_branch
  @type refinements :: %{optional(String.t()) => term()}

  @doc """
  Extract refinements that hold when `cond_ast` is true (`:true_branch`)
  or false (`:false_branch`).
  """
  @spec refine_along(tuple(), direction(), %{optional(String.t()) => term()}) :: refinements()
  def refine_along(cond_ast, direction, current_types) do
    pred = if direction == :true_branch, do: cond_ast, else: negate(cond_ast)
    extract(pred, current_types, %{})
  end

  # -- Negation ----------------------------------------------------------------

  @doc false
  def negate({:unary_op, _meta, [inner]}), do: inner

  def negate({:binary_op, meta, [l, r]}) do
    case Keyword.get(meta, :operator) do
      :== -> {:binary_op, Keyword.put(meta, :operator, :!=), [l, r]}
      :!= -> {:binary_op, Keyword.put(meta, :operator, :==), [l, r]}
      :< -> {:binary_op, Keyword.put(meta, :operator, :>=), [l, r]}
      :<= -> {:binary_op, Keyword.put(meta, :operator, :>), [l, r]}
      :> -> {:binary_op, Keyword.put(meta, :operator, :<=), [l, r]}
      :>= -> {:binary_op, Keyword.put(meta, :operator, :<), [l, r]}
      _ -> {:unary_op, [operator: :not], [{:binary_op, meta, [l, r]}]}
    end
  end

  def negate(other), do: {:unary_op, [operator: :not], [other]}

  # -- Extraction --------------------------------------------------------------

  defp extract({:binary_op, meta, [{:variable, _, name}, {:literal, _, _value}] = ops}, current, acc) do
    op = Keyword.get(meta, :operator)
    base = current_type(name, current)
    add_refinement(name, base, op, ops, meta, acc)
  end

  defp extract({:binary_op, meta, [{:literal, _, _value}, {:variable, _, name}] = ops}, current, acc) do
    op = Keyword.get(meta, :operator) |> flip()
    base = current_type(name, current)
    [l, r] = ops
    add_refinement(name, base, op, [r, l], meta, acc)
  end

  defp extract({:binary_op, meta, [a, b]}, current, acc) do
    case Keyword.get(meta, :operator) do
      :and ->
        acc1 = extract(a, current, acc)
        extract(b, current, acc1)

      _ ->
        acc
    end
  end

  defp extract({:function_call, meta, [{:variable, _, name}]}, current, acc) do
    case Keyword.get(meta, :name) do
      "is_int" -> Map.put(acc, name, :int)
      "is_float" -> Map.put(acc, name, :float)
      "is_string" -> Map.put(acc, name, :string)
      "is_bool" -> Map.put(acc, name, :bool)
      "is_atom" -> Map.put(acc, name, :atom)
      _ -> Map.put_new(acc, name, current_type(name, current))
    end
  end

  defp extract(_other, _current, acc), do: acc

  defp current_type(name, current), do: Map.get(current, name, :any)

  defp add_refinement(name, base, op, ops, meta, acc) do
    [_var, lit] = ops

    pred = {:binary_op, Keyword.put(meta, :operator, op), [{:variable, [], name}, lit]}

    refinement =
      case base do
        atom when is_atom(atom) -> Refinement.new(atom, name, pred)
        {:refinement, b, _, _} -> Refinement.new(b, name, pred)
        other -> other
      end

    Map.put(acc, name, refinement)
  end

  defp flip(:<), do: :>
  defp flip(:<=), do: :>=
  defp flip(:>), do: :<
  defp flip(:>=), do: :<=
  defp flip(other), do: other
end
