defmodule CureSpline.Float do
  @moduledoc """
  Float primitives that Cure reaches into via `@extern(Elixir.CureSpline.Float, ...)`.

  Cure's `/` operator currently lowers to Erlang's integer `div/2`, so genuine
  `Float`-returning division has to come from a host function. This module is
  the narrow seam that keeps the Cure code pure-looking while giving it real
  floating-point arithmetic.
  """

  @doc "Floating-point division. Mirrors Erlang's `/` for floats (and promotes ints)."
  @spec fdiv(number(), number()) :: float()
  def fdiv(a, b), do: a / b

  @doc "Promote an integer to a float. Useful when Cure hands us a literal `0` or `1`."
  @spec to_float(number()) :: float()
  def to_float(n) when is_integer(n), do: n * 1.0
  def to_float(n) when is_float(n), do: n
end
