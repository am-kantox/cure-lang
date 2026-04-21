defmodule Cure.Temporal.Formula do
  @moduledoc """
  LTL (Linear Temporal Logic) formulae for the `temporal` container
  (v0.27.0).

  Formulae are represented as tagged tuples so they can be pattern-
  matched, pretty-printed, and compared structurally. Smart
  constructors are provided for each operator so callers never have
  to build tuples directly.

  ## Supported operators

  Propositional:

  - `atom(state_name)` -- true in a given state iff the system is in `state_name`.
  - `not_(p)`          -- negation.
  - `and_(p, q)`       -- conjunction.
  - `or_(p, q)`        -- disjunction.
  - `implies(p, q)`    -- material implication (`not p or q`).
  - `tt/0`, `ff/0`     -- tautology / contradiction.

  Temporal:

  - `always(p)`        -- G p, `p` holds at every future state.
  - `eventually(p)`    -- F p, `p` holds at some future state.
  - `never(p)`         -- `always(not_(p))`.
  - `next_(p)`         -- X p, `p` holds in the next state.
  - `until(p, q)`      -- `p U q`, `p` holds until `q` becomes true
                          and `q` eventually becomes true.

  ## Representation

  Each formula is a 2-tuple `{op, children}` where `children` is a
  list of sub-formulae (or `[state_name]` for atoms). This shape makes
  structural recursion over formulae trivial.
  """

  @type state_name :: String.t()
  @type t ::
          :tt
          | :ff
          | {:atom, [state_name]}
          | {:not_, [t()]}
          | {:and_, [t()]}
          | {:or_, [t()]}
          | {:implies, [t()]}
          | {:always, [t()]}
          | {:eventually, [t()]}
          | {:next_, [t()]}
          | {:until, [t()]}

  # -- Smart constructors ----------------------------------------------------

  @doc "True everywhere."
  @spec tt() :: t()
  def tt, do: :tt

  @doc "False everywhere."
  @spec ff() :: t()
  def ff, do: :ff

  @doc "Atomic state proposition."
  @spec atom(state_name()) :: t()
  def atom(state) when is_binary(state), do: {:atom, [state]}

  @doc "Logical negation."
  @spec not_(t()) :: t()
  def not_(:tt), do: :ff
  def not_(:ff), do: :tt
  def not_({:not_, [p]}), do: p
  def not_(p), do: {:not_, [p]}

  @doc "Conjunction."
  @spec and_(t(), t()) :: t()
  def and_(:tt, q), do: q
  def and_(p, :tt), do: p
  def and_(:ff, _), do: :ff
  def and_(_, :ff), do: :ff
  def and_(p, q), do: {:and_, [p, q]}

  @doc "Disjunction."
  @spec or_(t(), t()) :: t()
  def or_(:tt, _), do: :tt
  def or_(_, :tt), do: :tt
  def or_(:ff, q), do: q
  def or_(p, :ff), do: p
  def or_(p, q), do: {:or_, [p, q]}

  @doc "Material implication."
  @spec implies(t(), t()) :: t()
  def implies(p, q), do: or_(not_(p), q)

  @doc "G p -- p holds at every future state."
  @spec always(t()) :: t()
  def always(:tt), do: :tt
  def always(:ff), do: :ff
  def always(p), do: {:always, [p]}

  @doc "F p -- p holds at some future state."
  @spec eventually(t()) :: t()
  def eventually(:tt), do: :tt
  def eventually(:ff), do: :ff
  def eventually(p), do: {:eventually, [p]}

  @doc "Never p -- always not p."
  @spec never(t()) :: t()
  def never(p), do: always(not_(p))

  @doc "X p -- p holds in the next state."
  @spec next_(t()) :: t()
  def next_(p), do: {:next_, [p]}

  @doc "p U q -- p holds until q does, and q eventually holds."
  @spec until(t(), t()) :: t()
  def until(p, q), do: {:until, [p, q]}

  # -- Pretty-printing --------------------------------------------------------

  @doc """
  Render a formula as a human-readable string.
  """
  @spec show(t()) :: String.t()
  def show(:tt), do: "tt"
  def show(:ff), do: "ff"
  def show({:atom, [s]}), do: s
  def show({:not_, [p]}), do: "!(" <> show(p) <> ")"
  def show({:and_, [p, q]}), do: "(" <> show(p) <> " and " <> show(q) <> ")"
  def show({:or_, [p, q]}), do: "(" <> show(p) <> " or " <> show(q) <> ")"
  def show({:implies, [p, q]}), do: "(" <> show(p) <> " -> " <> show(q) <> ")"
  def show({:always, [p]}), do: "always " <> show(p)
  def show({:eventually, [p]}), do: "eventually " <> show(p)
  def show({:next_, [p]}), do: "next " <> show(p)
  def show({:until, [p, q]}), do: "(" <> show(p) <> " until " <> show(q) <> ")"
  def show(other), do: inspect(other)

  # -- Collection helpers -----------------------------------------------------

  @doc """
  Return the set of state names that appear as atoms anywhere inside
  a formula. Useful for cross-checking against an FSM's state universe.
  """
  @spec atoms(t()) :: [state_name()]
  def atoms(formula) do
    formula
    |> do_atoms([])
    |> Enum.uniq()
    |> Enum.sort()
  end

  defp do_atoms(:tt, acc), do: acc
  defp do_atoms(:ff, acc), do: acc
  defp do_atoms({:atom, [s]}, acc), do: [s | acc]

  defp do_atoms({_op, children}, acc) when is_list(children) do
    Enum.reduce(children, acc, &do_atoms/2)
  end
end
