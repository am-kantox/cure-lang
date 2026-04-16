defmodule Cure.Types.Reduce do
  @moduledoc """
  Type-level expression normalization for the Cure type system.

  Many dependent-type idioms in Cure require comparing types up to
  *definitional equality*. For example:

      fn append(xs: Vector(T, m), ys: Vector(T, n)) -> Vector(T, m + n)

  At the call site `append(a, b)` where `a : Vector(T, 3)` and
  `b : Vector(T, 5)`, we want the inferred result type
  `Vector(T, 3 + 5)` to be considered equal to `Vector(T, 8)` without
  ever leaving the type checker.

  This module performs a small, terminating, syntactic reduction over
  type-level expressions:

  - **Arithmetic**: `+`, `-`, `*`, `/` on integer literals.
  - **Boolean**: `and`, `or`, `not`, comparisons over literals.
  - **Substitution**: replace free variables with concrete value ASTs.
  - **Sigma projection**: `pair.0`, `pair.1` when `pair` is a literal
    tuple.

  Anything not reducible is left untouched. The result is *always*
  syntactically smaller-or-equal to the input.

  ## Usage

      iex> ast = {:binary_op, [operator: :+], [
      ...>   {:literal, [subtype: :integer], 3},
      ...>   {:literal, [subtype: :integer], 5}
      ...> ]}
      iex> Cure.Types.Reduce.normalize(ast, %{})
      {:literal, [subtype: :integer], 8}

      iex> ast = {:binary_op, [operator: :+], [
      ...>   {:variable, [], "n"},
      ...>   {:literal, [subtype: :integer], 1}
      ...> ]}
      iex> Cure.Types.Reduce.normalize(ast, %{"n" => {:literal, [subtype: :integer], 4}})
      {:literal, [subtype: :integer], 5}

  ## Definitional equality

  `equal?/3` compares two type-level expressions after normalization.
  This is the workhorse that makes dependent-type return signatures
  feel "smart" without dragging in a full SMT call for trivial cases.
  """

  @type ast :: tuple() | atom() | number() | binary()
  @type bindings :: %{optional(String.t()) => ast()}

  # -- Public API --------------------------------------------------------------

  @doc """
  Normalize a type-level expression AST under the given bindings.

  Bindings map free variable names to their concrete AST values.
  Unknown variables are left as-is.
  """
  @spec normalize(ast(), bindings()) :: ast()
  def normalize(ast, bindings \\ %{}) do
    do_normalize(ast, bindings)
  end

  @doc """
  True when two type-level expressions reduce to the same normal form.

  This is the definitional-equality predicate the type checker uses
  before falling back to SMT.
  """
  @spec equal?(ast(), ast(), bindings()) :: boolean()
  def equal?(a, b, bindings \\ %{}) do
    normalize(a, bindings) == normalize(b, bindings)
  end

  @doc """
  Substitute every occurrence of free variables matching `bindings`.

  Unlike `normalize/2`, no arithmetic reduction is performed.
  """
  @spec substitute(ast(), bindings()) :: ast()
  def substitute(ast, bindings) do
    do_substitute(ast, bindings)
  end

  # -- Reduction Engine --------------------------------------------------------

  defp do_normalize({:variable, _meta, name} = ast, bindings) when is_binary(name) do
    case Map.get(bindings, name) do
      nil -> ast
      replacement -> do_normalize(replacement, bindings)
    end
  end

  defp do_normalize({:literal, _meta, _value} = lit, _bindings), do: lit

  defp do_normalize({:binary_op, meta, [left, right]}, bindings) do
    operator = Keyword.get(meta, :operator)
    l = do_normalize(left, bindings)
    r = do_normalize(right, bindings)

    case fold_binary(operator, l, r) do
      {:ok, value} -> literal_for(operator, value, meta)
      :no_fold -> {:binary_op, meta, [l, r]}
    end
  end

  defp do_normalize({:unary_op, meta, [operand]}, bindings) do
    operator = Keyword.get(meta, :operator)
    o = do_normalize(operand, bindings)

    case fold_unary(operator, o) do
      {:ok, value} -> literal_for(operator, value, meta)
      :no_fold -> {:unary_op, meta, [o]}
    end
  end

  defp do_normalize({:tuple, meta, elements}, bindings) when is_list(elements) do
    {:tuple, meta, Enum.map(elements, &do_normalize(&1, bindings))}
  end

  defp do_normalize({:list, meta, elements}, bindings) when is_list(elements) do
    {:list, meta, Enum.map(elements, &do_normalize(&1, bindings))}
  end

  defp do_normalize({:function_call, meta, args}, bindings) do
    name = Keyword.get(meta, :name, "")
    new_args = Enum.map(args, &do_normalize(&1, bindings))

    cond do
      name == "fst" and length(new_args) == 1 ->
        case hd(new_args) do
          {:tuple, _, [a, _b]} -> a
          _ -> {:function_call, meta, new_args}
        end

      name == "snd" and length(new_args) == 1 ->
        case hd(new_args) do
          {:tuple, _, [_a, b]} -> b
          _ -> {:function_call, meta, new_args}
        end

      true ->
        {:function_call, meta, new_args}
    end
  end

  defp do_normalize({tag, meta, children}, bindings) when is_list(children) do
    {tag, meta, Enum.map(children, &do_normalize(&1, bindings))}
  end

  defp do_normalize(other, _bindings), do: other

  # -- Substitution (no folding) -----------------------------------------------

  defp do_substitute({:variable, _meta, name} = ast, bindings) when is_binary(name) do
    Map.get(bindings, name, ast)
  end

  defp do_substitute({tag, meta, children}, bindings) when is_list(children) do
    {tag, meta, Enum.map(children, &do_substitute(&1, bindings))}
  end

  defp do_substitute(other, _bindings), do: other

  # -- Folding -----------------------------------------------------------------

  defp fold_binary(op, {:literal, _, a}, {:literal, _, b})
       when is_integer(a) and is_integer(b) do
    case op do
      :+ -> {:ok, a + b}
      :- -> {:ok, a - b}
      :* -> {:ok, a * b}
      :/ when b != 0 -> {:ok, div(a, b)}
      :% when b != 0 -> {:ok, rem(a, b)}
      :== -> {:ok, a == b}
      :!= -> {:ok, a != b}
      :< -> {:ok, a < b}
      :<= -> {:ok, a <= b}
      :> -> {:ok, a > b}
      :>= -> {:ok, a >= b}
      _ -> :no_fold
    end
  end

  defp fold_binary(op, {:literal, _, a}, {:literal, _, b})
       when is_number(a) and is_number(b) do
    case op do
      :+ -> {:ok, a + b}
      :- -> {:ok, a - b}
      :* -> {:ok, a * b}
      :/ when b != 0 -> {:ok, a / b}
      :== -> {:ok, a == b}
      :!= -> {:ok, a != b}
      :< -> {:ok, a < b}
      :<= -> {:ok, a <= b}
      :> -> {:ok, a > b}
      :>= -> {:ok, a >= b}
      _ -> :no_fold
    end
  end

  defp fold_binary(op, {:literal, _, a}, {:literal, _, b})
       when is_boolean(a) and is_boolean(b) do
    case op do
      :and -> {:ok, a and b}
      :or -> {:ok, a or b}
      :== -> {:ok, a == b}
      :!= -> {:ok, a != b}
      _ -> :no_fold
    end
  end

  defp fold_binary(_, _, _), do: :no_fold

  defp fold_unary(:-, {:literal, _, n}) when is_number(n), do: {:ok, -n}
  defp fold_unary(:not, {:literal, _, b}) when is_boolean(b), do: {:ok, not b}
  defp fold_unary(_, _), do: :no_fold

  # -- Result construction -----------------------------------------------------

  defp literal_for(_op, value, meta) when is_integer(value) do
    {:literal, Keyword.put(meta, :subtype, :integer), value}
    |> drop_op_meta()
  end

  defp literal_for(_op, value, meta) when is_float(value) do
    {:literal, Keyword.put(meta, :subtype, :float), value}
    |> drop_op_meta()
  end

  defp literal_for(_op, value, meta) when is_boolean(value) do
    {:literal, Keyword.put(meta, :subtype, :boolean), value}
    |> drop_op_meta()
  end

  defp drop_op_meta({:literal, meta, value}) do
    {:literal, Keyword.delete(meta, :operator), value}
  end
end
