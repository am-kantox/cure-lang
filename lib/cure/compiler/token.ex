defmodule Cure.Compiler.Token do
  @moduledoc """
  Token representation for the Cure lexer.

  Every token carries its type, value, and source location (line + column).
  """

  @type t :: %__MODULE__{
          type: atom(),
          value: term(),
          line: pos_integer(),
          col: pos_integer()
        }

  @enforce_keys [:type, :value, :line, :col]
  defstruct [:type, :value, :line, :col]

  @doc "Create a new token."
  @spec new(atom(), term(), pos_integer(), pos_integer()) :: t()
  def new(type, value, line, col) do
    %__MODULE__{type: type, value: value, line: line, col: col}
  end
end
