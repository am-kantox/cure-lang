defmodule Cure.Types.Sigma do
  @moduledoc """
  Sigma types (dependent pairs) for the Cure type system.

  A Sigma type pairs a value with a type that may *depend on that value*:

      type Sized(T) = Sigma(n: Nat, Vector(T, n))

  This means: "a pair of a natural number `n` and a vector of `T` of
  exactly length `n`". The second component's type literally references
  the first component's value.

  ## Representation

  Internally, a Sigma type is represented as:

      {:sigma, var_name :: String.t(), fst_type :: term(), snd_ast :: tuple()}

  where `snd_ast` is a parser type-AST node that may reference `var_name`.

  ## Surface syntax

  Cure recognises three forms on the surface:

  - `Sigma(T1, T2)` -- non-dependent: same as `%[T1, T2]` (`var = "_"`).
  - `Sigma(name: T1, T2)` -- dependent: `name` is bound in `T2`.
  - `(name: T1 ** T2)` -- shorthand sugar (recognised by the resolver).

  The first form preserves backward compatibility; the second is the
  Idris-style sugar; the third matches mathematical `Sigma_n: Nat. Vec T n`
  notation.

  ## Subtyping

  - `{:sigma, _, A1, B1} <: {:sigma, _, A2, B2}`
    when `A1 <: A2` and `resolve(B1) <: resolve(B2)`.
  - `{:sigma, _, A, B} <: %[A', B']` when both component subtypes hold
    (forgetting dependency).

  ## Pattern matching

  A pair value `(x, v)` of Sigma type binds `x` with type `A` and `v`
  with type `B[x := value of x]`.
  """

  alias Cure.Types.Type

  @type t :: {:sigma, String.t(), term(), tuple() | nil}

  # -- Construction ------------------------------------------------------------

  @doc "Build a Sigma type."
  @spec new(String.t(), term(), tuple() | nil) :: t()
  def new(var_name, fst_type, snd_ast)
      when is_binary(var_name) do
    {:sigma, var_name, fst_type, snd_ast}
  end

  @doc "True when `t` is a Sigma type."
  @spec sigma?(term()) :: boolean()
  def sigma?({:sigma, v, _f, _s}) when is_binary(v), do: true
  def sigma?(_), do: false

  @doc "Variable name bound by the Sigma."
  @spec var(t()) :: String.t()
  def var({:sigma, v, _, _}), do: v

  @doc "First component type."
  @spec fst(t()) :: term()
  def fst({:sigma, _, f, _}), do: f

  @doc "Second component AST (may reference `var`)."
  @spec snd_ast(t()) :: tuple() | nil
  def snd_ast({:sigma, _, _, s}), do: s

  @doc """
  Resolve a Sigma type from a parser AST function-call shape.

  Recognises `Sigma(...)` and `DPair(...)` as the named constructors, and
  delegates to `Type.resolve/1` for the component types.

  Accepts:
  - `Sigma(T1, T2)` -- two type arguments.
  - `Sigma(name: T1, T2)` -- a `param` shaped first argument carrying the
    bound name and the first type.
  """
  @spec from_function_call(keyword(), [tuple()]) :: t() | :not_sigma
  def from_function_call(meta, args) do
    name = Keyword.get(meta, :name, "")

    if name in ["Sigma", "DPair"] do
      case args do
        [{:param, pmeta, pname}, snd_ast] ->
          fst_ast = Keyword.get(pmeta, :type)
          fst = Type.resolve(fst_ast)
          new(pname, fst, snd_ast)

        [fst_ast, snd_ast] ->
          fst = Type.resolve(fst_ast)
          new("_", fst, snd_ast)

        _ ->
          :not_sigma
      end
    else
      :not_sigma
    end
  end

  @doc """
  Compute the second component's type at a concrete first value.

  `bind` substitutes occurrences of the bound variable in `snd_ast`
  with `value_ast`, then resolves the result.
  """
  @spec instantiate(t(), tuple()) :: term()
  def instantiate({:sigma, var_name, _fst, snd_ast}, value_ast) do
    case snd_ast do
      nil ->
        :any

      ast ->
        substituted = substitute(ast, var_name, value_ast)
        Type.resolve(substituted)
    end
  end

  @doc """
  Subtype rule for two Sigma types with the same arity.
  """
  @spec subtype?(t(), t()) :: boolean()
  def subtype?({:sigma, _v1, f1, s1}, {:sigma, _v2, f2, s2}) do
    Type.subtype?(f1, f2) and Type.subtype?(Type.resolve(s1), Type.resolve(s2))
  end

  def subtype?({:sigma, _v, f, s}, {:tuple, [a, b]}) do
    Type.subtype?(f, a) and Type.subtype?(Type.resolve(s), b)
  end

  def subtype?({:tuple, [a, b]}, {:sigma, _v, f, s}) do
    Type.subtype?(a, f) and Type.subtype?(b, Type.resolve(s))
  end

  def subtype?(_, _), do: false

  @doc "Human-readable rendering."
  @spec display(t()) :: String.t()
  def display({:sigma, "_", f, s}) do
    "Sigma(#{Type.display(f)}, #{Type.display(Type.resolve(s))})"
  end

  def display({:sigma, v, f, s}) do
    "Sigma(#{v}: #{Type.display(f)}, #{Type.display(Type.resolve(s))})"
  end

  # -- Substitution ------------------------------------------------------------

  defp substitute({:variable, _meta, name} = ast, var, repl) do
    if name == var, do: repl, else: ast
  end

  defp substitute({tag, meta, children}, var, repl) when is_list(children) do
    {tag, meta, Enum.map(children, &substitute(&1, var, repl))}
  end

  defp substitute(other, _var, _repl), do: other
end
