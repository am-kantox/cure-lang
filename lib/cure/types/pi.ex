defmodule Cure.Types.Pi do
  @moduledoc """
  Pi types -- dependent function types -- for the Cure type system.

  A Pi type is a function type whose return type may *depend on the
  arguments*. Idris writes this as `(n : Nat) -> Vect n Int`. In Cure
  the surface form looks like:

      fn append(xs: Vector(T, m), ys: Vector(T, n)) -> Vector(T, m + n)

  Internally we represent this as:

      {:pi, [{name, type, mode}, ...], ret_type_ast}

  where `mode` is one of:

  - `:explicit` -- normal explicit parameter (the default).
  - `:implicit` -- inferred at the call site by `Cure.Types.Unify`.
  - `:erased`   -- type-only parameter that has no runtime presence.

  `ret_type_ast` is a parser type-AST node that may freely reference
  the parameter names. At call sites, the type checker substitutes
  argument expressions into `ret_type_ast`, normalises with
  `Cure.Types.Reduce`, and resolves the result.

  ## Backward compatibility

  Plain `{:fun, params, ret}` is treated as Pi with all-explicit
  parameters whose names are anonymous and a return type that does
  not depend on any parameter. Existing code paths in the type
  checker continue to work unchanged.
  """

  alias Cure.Types.{Type, Reduce}

  @type mode :: :explicit | :implicit | :erased
  @type param :: {String.t(), term(), mode()}
  @type t :: {:pi, [param()], tuple()}

  # -- Construction ------------------------------------------------------------

  @doc "Build a Pi type."
  @spec new([param()], tuple()) :: t()
  def new(params, ret_ast), do: {:pi, params, ret_ast}

  @doc "True when `t` is a Pi type."
  @spec pi?(term()) :: boolean()
  def pi?({:pi, _ps, _ret}), do: true
  def pi?(_), do: false

  @doc "Lift a plain function type to a Pi with anonymous params."
  @spec from_fun(term()) :: t()
  def from_fun({:fun, params, ret}) do
    p = Enum.with_index(params, fn t, i -> {"_#{i}", t, :explicit} end)
    {:pi, p, type_to_ast(ret)}
  end

  def from_fun({:effun, params, ret, _effs}) do
    from_fun({:fun, params, ret})
  end

  def from_fun(other), do: other

  @doc "Project Pi parameters."
  @spec params(t()) :: [param()]
  def params({:pi, ps, _}), do: ps

  @doc "Project Pi return-type AST."
  @spec return_ast(t()) :: tuple()
  def return_ast({:pi, _ps, ret}), do: ret

  @doc """
  Compute the *applied* return type of a Pi at a list of call-site argument ASTs.

  - Builds a binding map from explicit parameter names to argument ASTs.
  - Substitutes through the return-type AST.
  - Normalises the substituted AST with `Cure.Types.Reduce`.
  - Resolves the normalised AST back to a `Cure.Types.Type` value.
  """
  @spec apply_return(t(), [tuple()]) :: term()
  def apply_return({:pi, params, ret_ast}, args) do
    explicit_params = Enum.filter(params, fn {_, _, m} -> m == :explicit end)

    bindings =
      explicit_params
      |> Enum.zip(args)
      |> Enum.into(%{}, fn {{name, _t, _m}, arg_ast} -> {name, arg_ast} end)

    ret_ast
    |> Reduce.substitute(bindings)
    |> Reduce.normalize(bindings)
    |> Type.resolve()
  end

  @doc """
  Erase implicit / erased parameters, leaving only explicit ones.

  Used by codegen to produce a runtime-faithful function arity.
  """
  @spec erase_implicits(t()) :: {:fun, [term()], term()}
  def erase_implicits({:pi, params, ret_ast}) do
    explicit = Enum.filter(params, fn {_, _, m} -> m == :explicit end)
    param_types = Enum.map(explicit, fn {_, t, _} -> t end)
    {:fun, param_types, Type.resolve(ret_ast)}
  end

  # -- Internal: degrade a resolved type back to an AST node -------------------

  # When we lift a plain {:fun, _, _}, the return is already a resolved type.
  # Wrap it in a synthetic AST shape so Reduce treats it opaquely.
  defp type_to_ast(t), do: {:type_value, [], t}
end
