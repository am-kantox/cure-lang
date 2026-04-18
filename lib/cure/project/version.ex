defmodule Cure.Project.Version do
  @moduledoc """
  Semantic-version and version-constraint parser (v0.19.0).

  Versions are three-component `MAJOR.MINOR.PATCH` triples with an
  optional pre-release tag (`-rc.1`, `-alpha`, ...). Build metadata
  (`+sha.<hash>`) is accepted and retained but ignored for ordering.

  Constraint grammar:

      constraint := simple (\"and\" simple)*
      simple     := op? version
      op         := \"~>\" | \">=\" | \"<=\" | \">\" | \"<\" | \"==\"

  `~>` is the "pessimistic" operator: `~> MAJOR.MINOR` matches every
  version `>= MAJOR.MINOR.0 and < MAJOR+1.0.0`; `~> MAJOR.MINOR.PATCH`
  matches every version `>= MAJOR.MINOR.PATCH and < MAJOR.MINOR+1.0`.

  All constraints are parsed into a flat list of `{op, version}` pairs
  with implicit `and` semantics.
  """

  @type version :: {non_neg_integer(), non_neg_integer(), non_neg_integer(), String.t() | nil}
  @type op :: :~> | :>= | :<= | :> | :< | :==
  @type constraint :: [{op(), version()}]

  @op_tokens ["~>", ">=", "<=", "==", ">", "<"]

  # -- Version parsing --------------------------------------------------------

  @doc """
  Parse a version string into a `{major, minor, patch, pre}` tuple.

  Returns `{:ok, version}` or `{:error, reason}`.
  """
  @spec parse(String.t()) :: {:ok, version()} | {:error, atom()}
  def parse(nil), do: {:error, :nil_version}
  def parse(""), do: {:error, :empty_version}

  def parse(text) when is_binary(text) do
    # Strip build metadata (`+sha.abc`) if present; it does not affect ordering.
    {text, _build} =
      case String.split(text, "+", parts: 2) do
        [v, b] -> {v, b}
        [v] -> {v, nil}
      end

    {core, pre} =
      case String.split(text, "-", parts: 2) do
        [v, p] -> {v, p}
        [v] -> {v, nil}
      end

    case String.split(core, ".") do
      [maj, min, patch] ->
        with {maj, ""} <- Integer.parse(maj),
             {min, ""} <- Integer.parse(min),
             {patch, ""} <- Integer.parse(patch) do
          {:ok, {maj, min, patch, pre}}
        else
          _ -> {:error, :invalid_version}
        end

      [maj, min] ->
        # MAJOR.MINOR auto-normalizes to MAJOR.MINOR.0 -- common for `~> 1.0`.
        with {maj, ""} <- Integer.parse(maj),
             {min, ""} <- Integer.parse(min) do
          {:ok, {maj, min, 0, pre}}
        else
          _ -> {:error, :invalid_version}
        end

      _ ->
        {:error, :invalid_version}
    end
  end

  @doc """
  Render a version tuple back into a canonical string.
  """
  @spec to_string(version()) :: String.t()
  def to_string({maj, min, patch, nil}), do: "#{maj}.#{min}.#{patch}"
  def to_string({maj, min, patch, pre}), do: "#{maj}.#{min}.#{patch}-#{pre}"

  @doc """
  Compare two versions. Returns `:lt`, `:eq`, or `:gt`.

  Pre-release tags make a version *older* than its no-tag equivalent
  (per SemVer: `1.0.0-alpha < 1.0.0`).
  """
  @spec compare(version(), version()) :: :lt | :eq | :gt
  def compare({ma, mi, pa, pra}, {mb, mib, pb, prb}) do
    cond do
      ma != mb -> compare_ints(ma, mb)
      mi != mib -> compare_ints(mi, mib)
      pa != pb -> compare_ints(pa, pb)
      pra == prb -> :eq
      pra == nil -> :gt
      prb == nil -> :lt
      pra < prb -> :lt
      true -> :gt
    end
  end

  defp compare_ints(a, b) when a < b, do: :lt
  defp compare_ints(a, b) when a > b, do: :gt
  defp compare_ints(_, _), do: :eq

  # -- Constraint parsing -----------------------------------------------------

  @doc """
  Parse a constraint string into a list of `{op, version}` pairs joined
  by implicit `and`.

      iex> Cure.Project.Version.parse_constraint("~> 1.0")
      {:ok, [{:~>, {1, 0, 0, nil}}]}
      iex> Cure.Project.Version.parse_constraint("~> 1.0 and < 1.5")
      {:ok, [{:~>, {1, 0, 0, nil}}, {:<, {1, 5, 0, nil}}]}
  """
  @spec parse_constraint(String.t()) :: {:ok, constraint()} | {:error, atom()}
  def parse_constraint(text) when is_binary(text) do
    text
    |> String.split(~r/\s+and\s+/, trim: true)
    |> Enum.reduce_while({:ok, []}, fn segment, {:ok, acc} ->
      case parse_simple(segment) do
        {:ok, pair} -> {:cont, {:ok, acc ++ [pair]}}
        err -> {:halt, err}
      end
    end)
  end

  defp parse_simple(segment) do
    segment = String.trim(segment)

    {op, rest} =
      Enum.find_value(@op_tokens, {:==, segment}, fn op ->
        if String.starts_with?(segment, op) do
          {atomize_op(op), String.trim_leading(segment, op) |> String.trim_leading()}
        else
          false
        end
      end)

    case parse(rest) do
      {:ok, v} -> {:ok, {op, normalize_for_op(op, v)}}
      {:error, _} = err -> err
    end
  end

  defp atomize_op("~>"), do: :~>
  defp atomize_op(">="), do: :>=
  defp atomize_op("<="), do: :<=
  defp atomize_op(">"), do: :>
  defp atomize_op("<"), do: :<
  defp atomize_op("=="), do: :==

  # `~> 1.0` is understood as a two-component version; normalize it to
  # `1.0.0` for downstream comparison.
  defp normalize_for_op(:~>, v), do: v
  defp normalize_for_op(_, v), do: v

  # -- Constraint satisfaction -----------------------------------------------

  @doc """
  Return `true` when `version` satisfies every clause in `constraint`.

  Constraint clauses are ANDed together.
  """
  @spec satisfies?(version(), constraint()) :: boolean()
  def satisfies?(version, constraint) when is_list(constraint) do
    Enum.all?(constraint, fn {op, v} -> satisfies_clause?(version, op, v) end)
  end

  defp satisfies_clause?(v, :==, target), do: compare(v, target) == :eq
  defp satisfies_clause?(v, :>=, target), do: compare(v, target) in [:gt, :eq]
  defp satisfies_clause?(v, :<=, target), do: compare(v, target) in [:lt, :eq]
  defp satisfies_clause?(v, :>, target), do: compare(v, target) == :gt
  defp satisfies_clause?(v, :<, target), do: compare(v, target) == :lt

  defp satisfies_clause?(v, :~>, {maj, min, _patch, _} = target) do
    # `~> X.Y.Z` or `~> X.Y`: `>= target and < next_floor`.
    # We treat the trailing 0 as meaning "any patch".
    lower_ok = compare(v, target) in [:gt, :eq]

    upper_bound =
      if :erlang.element(3, target) == 0 do
        {maj + 1, 0, 0, nil}
      else
        {maj, min + 1, 0, nil}
      end

    lower_ok and compare(v, upper_bound) == :lt
  end

  @doc """
  Render a constraint back into a canonical string.
  """
  @spec constraint_to_string(constraint()) :: String.t()
  def constraint_to_string(constraint) do
    constraint
    |> Enum.map(fn {op, v} -> "#{op_to_string(op)} #{__MODULE__.to_string(v)}" end)
    |> Enum.join(" and ")
  end

  defp op_to_string(:~>), do: "~>"
  defp op_to_string(:>=), do: ">="
  defp op_to_string(:<=), do: "<="
  defp op_to_string(:>), do: ">"
  defp op_to_string(:<), do: "<"
  defp op_to_string(:==), do: "=="
end
