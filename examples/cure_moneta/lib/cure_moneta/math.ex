defmodule CureMoneta.Math do
  @moduledoc """
  Float helpers exposed to `moneta.cure` via `@extern`.

  Cure's `/` operator lowers to Erlang integer `div/2`, so real float division
  and int-to-float promotion must come from the host VM. These three functions
  are the only FFI surface the Cure source needs for FX rate calculations.
  """

  @doc "Float division: `a / b`."
  @spec fdiv(number(), number()) :: float()
  def fdiv(a, b), do: a / b

  @doc "Promote an integer to a float."
  @spec int_to_float(integer()) :: float()
  def int_to_float(n), do: n * 1.0
end
