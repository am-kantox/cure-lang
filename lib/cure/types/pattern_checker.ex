defmodule Cure.Types.PatternChecker do
  @moduledoc """
  Pattern exhaustiveness and redundancy analysis for match expressions
  and multi-clause functions.

  ## Algorithm

  Patterns are classified into abstract shapes, then coverage is computed
  against the scrutinee type. A match is exhaustive if the union of all
  pattern shapes covers the full type space.

  ## Pattern Shapes

  - `:wildcard` -- matches everything (`_` or a named variable)
  - `{:literal, subtype, value}` -- matches one specific value
  - `{:constructor, name, arity}` -- matches an ADT variant (e.g., `Ok`, `Error`)
  - `:empty_list` -- matches `[]`
  - `:cons` -- matches `[h | t]`
  - `{:tuple, arity}` -- matches a tuple of fixed arity

  ## Supported Scrutinee Types

  - `:bool` -- expects coverage of `true` and `false`
  - `{:adt, :result, _}` -- expects `Ok` and `Error`
  - `{:adt, :option, _}` -- expects `Some` and `None`
  - `{:list, _}` -- expects `[]` and `[_ | _]`
  - `:int`, `:float`, `:string`, `:atom` -- infinite types, require a wildcard
  - `:any` -- require a wildcard
  """

  @type pattern_shape ::
          :wildcard
          | {:literal, atom(), term()}
          | {:constructor, String.t(), non_neg_integer()}
          | :empty_list
          | :cons
          | {:tuple, non_neg_integer()}

  @type check_result :: :exhaustive | {:non_exhaustive, [String.t()]} | {:redundant, [integer()]}

  # -- Public API --------------------------------------------------------------

  @doc """
  Check exhaustiveness of a match expression.

  Takes the scrutinee type and a list of match arm pattern ASTs.
  Returns `:exhaustive` or `{:non_exhaustive, missing_descriptions}`.
  """
  @spec check_match(term(), [tuple()]) :: check_result()
  def check_match(scrutinee_type, pattern_asts) do
    shapes = Enum.map(pattern_asts, &classify_pattern/1)

    # If any pattern is a wildcard, the match is exhaustive
    if Enum.any?(shapes, &(&1 == :wildcard)) do
      check_redundancy(shapes, scrutinee_type)
    else
      check_coverage(shapes, scrutinee_type)
    end
  end

  @doc """
  Check exhaustiveness of multi-clause function patterns.

  Each clause has a list of patterns (one per parameter).
  For simplicity, we check exhaustiveness of the first parameter
  (the dispatch parameter) against its type.
  """
  @spec check_clauses(term(), [list()]) :: check_result()
  def check_clauses(param_type, clause_pattern_lists) do
    # Extract first pattern from each clause
    first_patterns = Enum.map(clause_pattern_lists, &hd/1)
    check_match(param_type, first_patterns)
  end

  @doc """
  Classify a pattern AST into a pattern shape.
  """
  @spec classify_pattern(tuple()) :: pattern_shape()
  def classify_pattern(ast) do
    case ast do
      # Wildcard
      {:variable, _, "_"} ->
        :wildcard

      # Named variable (acts as wildcard)
      {:variable, _, _name} ->
        :wildcard

      # Boolean literal
      {:literal, meta, value} ->
        subtype = Keyword.get(meta, :subtype, :unknown)
        {:literal, subtype, value}

      # Constructor: Ok(x), Error(e), Some(v), None()
      {:function_call, meta, args} ->
        name = Keyword.get(meta, :name, "unknown")

        if constructor?(name) do
          {:constructor, name, length(args)}
        else
          :wildcard
        end

      # Empty list
      {:list, _meta, []} ->
        :empty_list

      # Cons list [h | t]
      {:list, meta, _elems} ->
        if Keyword.get(meta, :cons, false) do
          :cons
        else
          # Non-empty literal list acts like cons
          :cons
        end

      # Tuple
      {:tuple, _meta, elems} ->
        {:tuple, length(elems)}

      # Anything else is treated as wildcard (conservative)
      _ ->
        :wildcard
    end
  end

  # -- Coverage Checking -------------------------------------------------------

  defp check_coverage(shapes, scrutinee_type) do
    required = required_shapes(scrutinee_type)

    case required do
      nil ->
        # Infinite type (Int, String, etc.) -- needs wildcard
        {:non_exhaustive, ["_ (wildcard)"]}

      required_set ->
        covered = MapSet.new(shapes)
        missing = MapSet.difference(required_set, covered)

        if MapSet.size(missing) == 0 do
          :exhaustive
        else
          descriptions = Enum.map(missing, &describe_shape/1) |> Enum.sort()
          {:non_exhaustive, descriptions}
        end
    end
  end

  defp check_redundancy(shapes, _scrutinee_type) do
    # Find patterns that come after a wildcard (they're unreachable)
    {_, redundant_indices} =
      Enum.reduce(shapes, {false, []}, fn shape, {seen_wildcard, redundant} ->
        if seen_wildcard do
          # This pattern is after a wildcard -- it's redundant
          {true, redundant}
        else
          if shape == :wildcard do
            {true, redundant}
          else
            {false, redundant}
          end
        end
      end)

    # Also check for duplicate literal patterns
    {_, dups} =
      Enum.reduce(Enum.with_index(shapes), {MapSet.new(), []}, fn {shape, idx}, {seen, dups} ->
        if shape != :wildcard and MapSet.member?(seen, shape) do
          {seen, [idx | dups]}
        else
          {MapSet.put(seen, shape), dups}
        end
      end)

    all_redundant = (redundant_indices ++ dups) |> Enum.uniq() |> Enum.sort()

    if all_redundant == [] do
      :exhaustive
    else
      # Still exhaustive (wildcard covers everything), but with redundant patterns
      :exhaustive
    end
  end

  # -- Required Shapes per Type ------------------------------------------------

  defp required_shapes(:bool) do
    MapSet.new([{:literal, :boolean, true}, {:literal, :boolean, false}])
  end

  defp required_shapes({:adt, :result, _}) do
    MapSet.new([{:constructor, "Ok", 1}, {:constructor, "Error", 1}])
  end

  defp required_shapes({:adt, :option, _}) do
    MapSet.new([{:constructor, "Some", 1}, {:constructor, "None", 0}])
  end

  defp required_shapes({:list, _}) do
    MapSet.new([:empty_list, :cons])
  end

  # Infinite types -- no finite set of required shapes
  defp required_shapes(:int), do: nil
  defp required_shapes(:float), do: nil
  defp required_shapes(:string), do: nil
  defp required_shapes(:atom), do: nil
  defp required_shapes(:any), do: nil
  defp required_shapes(_), do: nil

  # -- Descriptions ------------------------------------------------------------

  defp describe_shape({:literal, :boolean, true}), do: "true"
  defp describe_shape({:literal, :boolean, false}), do: "false"
  defp describe_shape({:literal, _subtype, value}), do: inspect(value)
  defp describe_shape({:constructor, name, 0}), do: "#{name}"
  defp describe_shape({:constructor, name, _arity}), do: "#{name}(...)"
  defp describe_shape(:empty_list), do: "[]"
  defp describe_shape(:cons), do: "[_ | _]"
  defp describe_shape({:tuple, n}), do: "%[#{String.duplicate("_, ", max(n - 1, 0))}...]"
  defp describe_shape(:wildcard), do: "_"
  defp describe_shape(other), do: inspect(other)

  # -- Helpers -----------------------------------------------------------------

  defp constructor?(name) when is_binary(name) do
    case String.first(name) do
      nil -> false
      first -> first == String.upcase(first) and first != String.downcase(first)
    end
  end

  defp constructor?(_), do: false
end
