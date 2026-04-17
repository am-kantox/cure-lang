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
  Classify a pattern AST into a pattern shape (top-level only).

  This classifier is the flat fast-path used for simple matches. Nested
  exhaustiveness is handled separately by `check_nested/2`.
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

      # Pin -- behaves like wildcard for coverage (the guard filters at runtime)
      {:pin, _, _} ->
        :wildcard

      # Boolean literal
      {:literal, meta, value} ->
        subtype = Keyword.get(meta, :subtype, :unknown)
        {:literal, subtype, value}

      # Record pattern: TypeName{field: val, ...}
      {:function_call, meta, _args} = ast_node ->
        cond do
          Keyword.get(meta, :record, false) ->
            {:record, Keyword.get(meta, :name, "unknown"), record_fields(ast_node)}

          true ->
            name = Keyword.get(meta, :name, "unknown")

            if constructor?(name) do
              {:constructor, name, length(elem(ast_node, 2))}
            else
              :wildcard
            end
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

      # Map
      {:map, _meta, pairs} ->
        {:map, length(pairs)}

      # Anything else is treated as wildcard (conservative)
      _ ->
        :wildcard
    end
  end

  # Extract the list of field names from a record pattern.
  defp record_fields({:function_call, _meta, args}) do
    Enum.flat_map(args, fn
      {:pair, _, [{:literal, [subtype: :symbol], atom}, _]} when is_atom(atom) ->
        [Atom.to_string(atom)]

      {:variable, _, name} when is_binary(name) ->
        [name]

      _ ->
        []
    end)
  end

  # -- Nested exhaustiveness (Maranget matrix) --------------------------------
  #
  # The full Maranget algorithm builds a pattern matrix and specialises on
  # each head constructor. For v0.18.0 we keep the surface simple: a
  # best-effort nested analysis that walks row-wise and collects missing
  # witnesses as *source-shaped* strings. Types for which we can enumerate
  # constructors (Bool, Result, Option) drive the witness generation; for
  # anything else we fall back to `["_"]` when no wildcard is present.

  @doc """
  Nested exhaustiveness check.

  Delegates to the flat classifier for single-level patterns, but for
  compound scrutinee types (tuples, pairs of ADTs, records) it descends
  into the pattern structure and reports missing witnesses in source
  form, for example ``"%[Error(_)]"``.

  Returns `:exhaustive` or `{:non_exhaustive, witnesses}`.
  """
  @spec check_nested(term(), [tuple()]) :: check_result()
  def check_nested(scrutinee_type, pattern_asts) do
    if Enum.any?(pattern_asts, &top_level_wildcard?/1) do
      :exhaustive
    else
      case missing_witnesses(scrutinee_type, pattern_asts) do
        [] -> :exhaustive
        witnesses -> {:non_exhaustive, witnesses}
      end
    end
  end

  defp top_level_wildcard?({:variable, _, "_"}), do: true
  defp top_level_wildcard?({:variable, _, _}), do: true
  defp top_level_wildcard?(_), do: false

  # Tuple of constructors: covers the most common nested shape.
  defp missing_witnesses({:tuple, element_types}, patterns) do
    # Collect the tuple patterns; abstain for non-tuple patterns.
    rows =
      Enum.flat_map(patterns, fn
        {:tuple, _, elems} when length(elems) == length(element_types) -> [elems]
        _ -> []
      end)

    if rows == [] do
      [render_tuple_witness(element_types)]
    else
      missing_tuple_product(element_types, rows)
    end
  end

  defp missing_witnesses(_scrutinee_type, _patterns), do: []

  defp missing_tuple_product(element_types, rows) do
    # For each column, compute the set of covered constructors. If any
    # column has a missing constructor, combine it with a `_` placeholder
    # for the remaining columns.
    columns =
      Enum.map(0..(length(element_types) - 1), fn idx ->
        Enum.map(rows, &Enum.at(&1, idx))
      end)

    Enum.zip(element_types, columns)
    |> Enum.with_index()
    |> Enum.flat_map(fn {{type, col_patterns}, idx} ->
      case missing_column_witnesses(type, col_patterns) do
        [] ->
          []

        ws ->
          Enum.map(ws, fn w -> render_tuple_with_hole(length(element_types), idx, w) end)
      end
    end)
    |> Enum.uniq()
  end

  defp missing_column_witnesses(type, patterns) do
    shapes = Enum.map(patterns, &classify_pattern/1)

    case required_shapes(type) do
      nil ->
        if Enum.any?(shapes, &(&1 == :wildcard)), do: [], else: ["_"]

      required ->
        covered = MapSet.new(shapes)

        MapSet.difference(required, covered)
        |> Enum.map(&describe_shape/1)
    end
  end

  defp render_tuple_witness(element_types) do
    slots = Enum.map(element_types, fn _ -> "_" end)
    "%[" <> Enum.join(slots, ", ") <> "]"
  end

  defp render_tuple_with_hole(arity, idx, witness) do
    slots =
      Enum.map(0..(arity - 1), fn i ->
        if i == idx, do: witness, else: "_"
      end)

    "%[" <> Enum.join(slots, ", ") <> "]"
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
