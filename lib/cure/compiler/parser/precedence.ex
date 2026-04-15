defmodule Cure.Compiler.Parser.Precedence do
  @moduledoc """
  Operator binding power table for Cure's Pratt parser.

  Binding powers (BP) determine operator precedence. Higher BP binds tighter.
  For left-associative operators, right BP = left BP + 1.
  For right-associative operators, right BP = left BP.
  For non-associative operators, right BP = left BP + 1 (and the parser
  rejects chaining).

  ## Precedence Levels (lowest to highest)

  | BP | Operators               | Assoc  |
  |----|-------------------------|--------|
  | 10 | `\\|>`                   | left   |
  | 20 | `or`                    | left   |
  | 30 | `and`                   | left   |
  | 40 | `== != < > <= >=`       | none   |
  | 50 | `.. ..=`                | none   |
  | 60 | `<>`                    | right  |
  | 70 | `+ -`                   | left   |
  | 80 | `* / %`                 | left   |
  | 90 | prefix `-`, `not`       |        |
  | 100| `.`                     | left   |
  """

  @doc "Returns `{left_bp, right_bp}` for an infix operator token type, or `:not_infix`."
  @spec infix_bp(atom()) :: {pos_integer(), pos_integer()} | :not_infix
  def infix_bp(:pipe), do: {10, 11}
  def infix_bp(:or_op), do: {20, 21}
  def infix_bp(:and_op), do: {30, 31}
  # Comparison -- non-associative (right = left + 1)
  def infix_bp(:eq), do: {40, 41}
  def infix_bp(:neq), do: {40, 41}
  def infix_bp(:lt), do: {40, 41}
  def infix_bp(:gt), do: {40, 41}
  def infix_bp(:lte), do: {40, 41}
  def infix_bp(:gte), do: {40, 41}
  # Range -- non-associative
  def infix_bp(:range), do: {50, 51}
  def infix_bp(:range_inclusive), do: {50, 51}
  # String concat -- right-associative
  def infix_bp(:string_concat), do: {60, 60}
  # Additive -- left-associative
  def infix_bp(:plus), do: {70, 71}
  def infix_bp(:minus), do: {70, 71}
  # Multiplicative -- left-associative
  def infix_bp(:star), do: {80, 81}
  def infix_bp(:slash), do: {80, 81}
  def infix_bp(:percent), do: {80, 81}
  # Dot access -- left-associative
  def infix_bp(:dot), do: {100, 101}
  # Assignment operators (very low, right-assoc)
  def infix_bp(:assign), do: {5, 4}
  def infix_bp(:plus_assign), do: {5, 4}
  def infix_bp(:minus_assign), do: {5, 4}
  def infix_bp(:star_assign), do: {5, 4}
  def infix_bp(:slash_assign), do: {5, 4}
  def infix_bp(_), do: :not_infix

  @doc "Returns the right binding power for a prefix operator, or `:not_prefix`."
  @spec prefix_bp(atom()) :: pos_integer() | :not_prefix
  def prefix_bp(:minus), do: 90
  def prefix_bp(:not_op), do: 90
  def prefix_bp(_), do: :not_prefix

  @doc "Returns the operator category for a given token type."
  @spec operator_category(atom()) :: atom()
  def operator_category(type) when type in [:plus, :minus, :star, :slash, :percent], do: :arithmetic
  def operator_category(type) when type in [:eq, :neq, :lt, :gt, :lte, :gte], do: :comparison
  def operator_category(type) when type in [:and_op, :or_op], do: :boolean
  def operator_category(:string_concat), do: :string
  def operator_category(type) when type in [:range, :range_inclusive], do: :range
  def operator_category(:pipe), do: :pipe
  def operator_category(:dot), do: :access
  def operator_category(_), do: :unknown

  @doc "Returns the operator atom for a given token type."
  @spec operator_symbol(atom()) :: atom()
  def operator_symbol(:plus), do: :+
  def operator_symbol(:minus), do: :-
  def operator_symbol(:star), do: :*
  def operator_symbol(:slash), do: :/
  def operator_symbol(:percent), do: :rem
  def operator_symbol(:eq), do: :==
  def operator_symbol(:neq), do: :!=
  def operator_symbol(:lt), do: :<
  def operator_symbol(:gt), do: :>
  def operator_symbol(:lte), do: :<=
  def operator_symbol(:gte), do: :>=
  def operator_symbol(:and_op), do: :and
  def operator_symbol(:or_op), do: :or
  def operator_symbol(:not_op), do: :not
  def operator_symbol(:string_concat), do: :<>
  def operator_symbol(:range), do: :..
  def operator_symbol(:range_inclusive), do: :"..="
  def operator_symbol(:pipe), do: :|>
  def operator_symbol(:dot), do: :.
  def operator_symbol(:assign), do: :=
  def operator_symbol(:plus_assign), do: :"+="
  def operator_symbol(:minus_assign), do: :"-="
  def operator_symbol(:star_assign), do: :"*="
  def operator_symbol(:slash_assign), do: :"/="
  def operator_symbol(other), do: other
end
