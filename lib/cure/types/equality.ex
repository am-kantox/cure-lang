defmodule Cure.Types.Equality do
  @moduledoc """
  Propositional equality for the Cure type system.

  Equality types let programs *carry proof* that two terms are equal:

      Eq(T, a, b)

  is the type of proofs that `a` and `b` (both of type `T`) are
  definitionally equal. There is exactly one constructor:

      refl(x) : Eq(T, x, x)

  and exactly one eliminator:

      rewrite eq in expr

  which substitutes equal terms in the goal type while type-checking
  `expr`.

  ## Runtime behaviour

  Equality types and their proofs are *erased* at runtime. `refl(x)`
  compiles to the unit value `:cure_refl`; `rewrite eq in expr`
  compiles to `expr` unchanged. The entire mechanism lives in the
  type checker.

  ## Definitional vs propositional

  Cure's `Cure.Types.Reduce` already gives us *definitional* equality
  for closed type-level expressions. Propositional equality kicks in
  for the things definitional equality cannot prove on its own: open
  terms, recursively defined functions, and small lemmas the user
  states explicitly.

  ## Use case

      proof_plus_zero(n: Nat) -> Eq(Nat, n + 0, n) = refl(n)

      fn append_left_id(xs: Vector(T, n)) -> Vector(T, 0 + n) =
        rewrite plus_zero(n) in xs
  """

  alias Cure.Types.{Reduce, Type}

  @type t :: {:eq, term(), tuple(), tuple()}

  # -- Construction ------------------------------------------------------------

  @doc "Construct an equality type."
  @spec new(term(), tuple(), tuple()) :: t()
  def new(type, a_ast, b_ast), do: {:eq, type, a_ast, b_ast}

  @doc "True when `t` is an equality type."
  @spec equality?(term()) :: boolean()
  def equality?({:eq, _t, _a, _b}), do: true
  def equality?(_), do: false

  @doc """
  Type of `refl(x)` given the inferred type of `x`.

  `refl(x) : Eq(T, x, x)`
  """
  @spec refl_type(term(), tuple()) :: t()
  def refl_type(t, x_ast), do: {:eq, t, x_ast, x_ast}

  @doc """
  Check that `refl(x)` is well-typed at the expected `Eq(T, a, b)`.

  - `x` must have type `T`.
  - `a` and `b` must be definitionally equal to `x` (and hence to each
    other).
  """
  @spec check_refl(t(), tuple(), term()) :: :ok | {:error, String.t()}
  def check_refl({:eq, t, a, b}, x_ast, x_type) do
    cond do
      not Type.subtype?(x_type, t) ->
        {:error, "refl: expected term of type #{Type.display(t)}, got #{Type.display(x_type)}"}

      not Reduce.equal?(a, x_ast) ->
        {:error, "refl: left side #{display_ast(a)} not definitionally equal to #{display_ast(x_ast)}"}

      not Reduce.equal?(b, x_ast) ->
        {:error, "refl: right side #{display_ast(b)} not definitionally equal to #{display_ast(x_ast)}"}

      true ->
        :ok
    end
  end

  @doc """
  Apply a `rewrite eq in expr` step.

  Given an equality `eq : Eq(T, a, b)`, rewriting in a goal type
  substitutes occurrences of `a` with `b` (left-to-right by default),
  returning the rewritten goal.

  This does *not* type-check the inner expression itself; the caller
  is expected to do so against the rewritten goal.
  """
  @spec rewrite(t(), term()) :: term()
  def rewrite({:eq, _t, a_ast, b_ast}, goal) do
    case goal do
      tuple when is_tuple(tuple) ->
        rewrite_in(tuple, a_ast, b_ast)

      _ ->
        goal
    end
  end

  defp rewrite_in(node, a, b) do
    cond do
      Reduce.equal?(node, a) -> b
      is_tuple(node) -> rewrite_tuple(node, a, b)
      true -> node
    end
  end

  defp rewrite_tuple({tag, meta, children}, a, b) when is_list(children) do
    {tag, meta, Enum.map(children, &rewrite_in(&1, a, b))}
  end

  defp rewrite_tuple(other, _a, _b), do: other

  defp display_ast({:literal, _, v}), do: inspect(v)
  defp display_ast({:variable, _, n}), do: n
  defp display_ast(other), do: inspect(other)

  @doc """
  Erlang-side runtime constants for the equality machinery.

  - `refl_runtime_value/0` is what `refl(x)` lowers to in BEAM bytecode.
  """
  @spec refl_runtime_value() :: atom()
  def refl_runtime_value, do: :cure_refl
end
