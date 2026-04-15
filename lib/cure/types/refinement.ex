defmodule Cure.Types.Refinement do
  @moduledoc """
  Refinement type operations for the Cure type system.

  A refinement type constrains a base type with a logical predicate:
  `{x: Int | x > 0}` means "integers that are greater than zero".

  ## Representation

  Refinement types are represented as:
  `{:refinement, base_type, var_name, predicate_ast}`

  Where `predicate_ast` is a MetaAST expression that can be translated
  to SMT-LIB2 for verification.

  ## Operations

  - **Subtype checking**: `{x: Int | x > 0} <: {x: Int | x != 0}`
    proven via SMT: `forall x. x > 0 => x != 0`
  - **Satisfiability**: Verify a refinement type is not empty
  - **Construction**: Create refinement types from parser AST
  """

  alias Cure.SMT.Solver

  @type t :: {:refinement, atom(), String.t(), tuple()}

  @doc """
  Create a refinement type from its components.

  ## Example

      # {x: Int | x > 0}
      Refinement.new(:int, "x", pred_ast)
  """
  @spec new(atom(), String.t(), tuple()) :: t()
  def new(base_type, var_name, predicate_ast) do
    {:refinement, base_type, var_name, predicate_ast}
  end

  @doc "Check if a type is a refinement type."
  @spec refinement?(term()) :: boolean()
  def refinement?({:refinement, _, _, _}), do: true
  def refinement?(_), do: false

  @doc "Extract the base type from a refinement type."
  @spec base_type(t()) :: atom()
  def base_type({:refinement, base, _, _}), do: base

  @doc "Extract the variable name from a refinement type."
  @spec var_name(t()) :: String.t()
  def var_name({:refinement, _, var, _}), do: var

  @doc "Extract the predicate AST from a refinement type."
  @spec predicate(t()) :: tuple()
  def predicate({:refinement, _, _, pred}), do: pred

  @doc """
  Check refinement subtype: `sub <: sup`.

  Both types must be refinement types with the same base type.
  Returns `true` (proven), `false` (counterexample), or `:unknown`.
  """
  @spec subtype?(t() | atom(), t() | atom()) :: boolean() | :unknown
  def subtype?({:refinement, base, var, pred1}, {:refinement, base, _var2, pred2}) do
    # Same base type -- check predicate implication via SMT
    Solver.check_refinement_subtype(pred1, pred2, var, base)
  end

  # Refinement type is subtype of its base type (drop the constraint)
  def subtype?({:refinement, base, _, _}, base) when is_atom(base), do: true

  # Non-refinement is not a subtype of a refinement (unless it can be proven)
  def subtype?(base, {:refinement, base, _, _}) when is_atom(base), do: :unknown

  def subtype?(_, _), do: false

  @doc """
  Check if a refinement type is satisfiable (not empty).

  A refinement type `{x: T | P(x)}` is satisfiable if there exists
  at least one value of type T that satisfies P.
  """
  @spec satisfiable?(t()) :: boolean()
  def satisfiable?({:refinement, base, var, pred}) do
    Solver.is_satisfiable?(pred, var, base)
  end

  @doc """
  Create a refinement type from a parser type_annotation AST.

  The parser produces refinement types as:
  `{:type_annotation, [name: "NonZero", refinement: true], [var_ast, base_type_ast, predicate_ast]}`
  """
  @spec from_type_annotation(keyword(), list()) :: t() | nil
  def from_type_annotation(meta, children) do
    if Keyword.get(meta, :refinement) do
      case children do
        [{:variable, _, var_name}, base_ast, pred_ast] ->
          base = Cure.Types.Type.resolve(base_ast)
          new(base, var_name, pred_ast)

        _ ->
          nil
      end
    else
      nil
    end
  end
end
