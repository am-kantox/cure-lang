defmodule Cure.Bless.Advisor do
  @moduledoc """
  Maps structured error tuples to ranked, actionable fix suggestions.

  Each suggestion is a map:

      %{
        kind:        String.t(),    # short human label ("add return type", ...)
        description: String.t(),    # one-sentence explanation shown to the user
        patch:       (String.t() -> {:ok, String.t()} | {:error, String.t()}) | nil
      }

  `patch` is a function that, given the full source string, returns the
  patched source. It is `nil` when a machine-applicable rewrite is not
  available (e.g. refinement proofs that require domain knowledge).

  `suggest/2` is the only public entry point: it receives an error tuple
  (as returned by `Cure.Types.Checker.check_module/2`) and the full
  source text, and returns a list of suggestions ordered by confidence.
  """

  @type patch_fn :: (String.t() -> {:ok, String.t()} | {:error, String.t()})
  @type suggestion :: %{kind: String.t(), description: String.t(), patch: patch_fn() | nil}

  # -- Public API --------------------------------------------------------------

  @doc """
  Return a ranked list of fix suggestions for `error` within `source`.
  """
  @spec suggest(tuple(), String.t()) :: [suggestion()]
  def suggest(error, source)

  # -- Type mismatch -----------------------------------------------------------
  # The most common error: a function's body type disagrees with its declared
  # return type. Strategy: offer to remove the annotation (relying on
  # inference) OR widen the annotation to `Any` as a last resort.
  def suggest({:type_mismatch, message, meta}, _source) do
    line = Keyword.get(meta, :line, 0)

    cond do
      # "declared return type X but body has type Y" -- suggest removing annotation
      String.contains?(message, "declared return type") ->
        [
          %{
            kind: "remove return type",
            description: "Remove the return type annotation on line #{line} and let the checker infer it.",
            patch: fn src ->
              {:ok, remove_return_type_annotation(src, line)}
            end
          },
          %{
            kind: "annotate as Any",
            description: "Change the return type to `Any` to silence the mismatch (temporary).",
            patch: fn src ->
              {:ok, replace_return_type_annotation(src, line, "Any")}
            end
          }
        ]

      # Argument type mismatch in call -- suggest wrapping with a coercion
      String.contains?(message, "argument type mismatch") ->
        [
          %{
            kind: "inspect call site",
            description:
              "Check the argument types at the call site on line #{line}. " <>
                "The expected types are shown above.",
            patch: nil
          }
        ]

      true ->
        [
          %{
            kind: "inspect",
            description:
              "The type checker found a mismatch on line #{line}. " <>
                "Review the types shown above and adjust the annotation or body.",
            patch: nil
          }
        ]
    end
  end

  # -- Constraint violation ----------------------------------------------------
  # A guard constraint may be violated. Strategy: suggest adding a require/
  # guard clause at the call site.
  def suggest({:constraint_violation, message, meta}, _source) do
    line = Keyword.get(meta, :line, 0)

    [
      %{
        kind: "add guard",
        description:
          "Add a `when` guard at the call site on line #{line} to ensure the constraint " <>
            "is always satisfied. The violated constraint: #{message}",
        patch: nil
      }
    ]
  end

  # -- Unbound variable --------------------------------------------------------
  # Variable is used but not defined. Strategy: suggest common fixes
  # (let binding, parameter, typo). If `Synth` can find a well-typed
  # expression with the same short name, offer it.
  def suggest({:unbound_variable, message, meta}, _source) do
    line = Keyword.get(meta, :line, 0)
    name = extract_quoted(message)

    synth_candidates =
      if name && String.length(name) > 1 do
        Cure.Types.Synth.synthesise(name, %{}, %{}, max: 2, depth: 2)
      else
        []
      end

    base = [
      %{
        kind: "add let binding",
        description: "Define '#{name || "the variable"}' with a `let` binding before line #{line}.",
        patch: fn src ->
          {:ok, insert_let_binding_before(src, line, name || "??")}
        end
      }
    ]

    synth_fixes =
      Enum.map(synth_candidates, fn c ->
        %{
          kind: "synthesised replacement",
          description: "Replace reference with `#{c.expr}` (synthesised from local context, cost #{c.cost}).",
          patch: fn src ->
            {:ok, replace_identifier_on_line(src, line, name || "", c.expr)}
          end
        }
      end)

    base ++ synth_fixes
  end

  # -- Arity mismatch ----------------------------------------------------------
  def suggest({:arity_mismatch, message, meta}, _source) do
    line = Keyword.get(meta, :line, 0)

    [
      %{
        kind: "fix argument count",
        description:
          "The call on line #{line} has the wrong number of arguments. " <>
            message,
        patch: nil
      }
    ]
  end

  # -- Record field errors (E021) ----------------------------------------------
  def suggest({:unknown_record_field, message, meta}, _source) do
    line = Keyword.get(meta, :line, 0)

    [
      %{
        kind: "fix field name",
        description: "Unknown field on line #{line}. #{message}",
        patch: nil
      }
    ]
  end

  # -- Non-exhaustive match (E004/E025) ----------------------------------------
  def suggest({:non_exhaustive_match, message, meta}, _source) do
    line = Keyword.get(meta, :line, 0)
    missing = extract_missing_patterns(message)

    if missing != [] do
      [
        %{
          kind: "add wildcard arm",
          description:
            "Add a catch-all `_ -> ...` arm to the match on line #{line} " <>
              "to cover the missing patterns: #{Enum.join(missing, ", ")}.",
          patch: fn src ->
            {:ok, insert_wildcard_arm(src, line)}
          end
        }
      ]
    else
      [
        %{
          kind: "add wildcard arm",
          description: "Add a catch-all `_ -> ...` arm to the match on line #{line}.",
          patch: fn src -> {:ok, insert_wildcard_arm(src, line)} end
        }
      ]
    end
  end

  # -- Fallback ----------------------------------------------------------------
  def suggest(_error, _source), do: []

  # -- Patch helpers -----------------------------------------------------------

  # Remove a `-> ReturnType` annotation from a `fn` definition on `line`.
  # Only removes the annotation if the line contains `->` followed by a type
  # expression (not `=`), so body-level `->` in lambdas is not touched.
  defp remove_return_type_annotation(source, line) do
    update_line(source, line, fn l ->
      # Match `-> Type` between the closing `)` and the `=`
      Regex.replace(~r/\s*->\s*\S+\s*(?==\s)/, l, " ", global: false)
    end)
  end

  defp replace_return_type_annotation(source, line, new_type) do
    update_line(source, line, fn l ->
      Regex.replace(~r/(?<=\))\s*->\s*\S+/, l, " -> #{new_type}", global: false)
    end)
  end

  defp insert_let_binding_before(source, line, name) do
    insert_at_line(source, line - 1, "  let #{name} = ??\n")
  end

  defp replace_identifier_on_line(source, line, old_name, new_expr) do
    update_line(source, line, fn l ->
      String.replace(l, old_name, new_expr, global: false)
    end)
  end

  defp insert_wildcard_arm(source, line) do
    insert_at_line(source, line + 1, "  _ -> throw \"unhandled case\"\n")
  end

  # -- String utilities --------------------------------------------------------

  defp update_line(source, line_num, fun) when line_num > 0 do
    lines = String.split(source, "\n")
    idx = line_num - 1

    if idx >= 0 and idx < length(lines) do
      updated = List.update_at(lines, idx, fun)
      Enum.join(updated, "\n")
    else
      source
    end
  end

  defp update_line(source, _line_num, _fun), do: source

  defp insert_at_line(source, after_line, text) do
    lines = String.split(source, "\n")
    {before, rest} = Enum.split(lines, after_line)
    Enum.join(before ++ [text | rest], "\n")
  end

  # Extract a single-quoted name from an error message, e.g.:
  # "undefined variable 'foo'" -> "foo"
  defp extract_quoted(message) do
    case Regex.run(~r/'([^']+)'/, message) do
      [_, name] -> name
      _ -> nil
    end
  end

  # Extract missing pattern names from a non-exhaustive message.
  defp extract_missing_patterns(message) do
    case Regex.run(~r/missing:\s*(.+)$/, message) do
      [_, rest] ->
        rest |> String.split(",") |> Enum.map(&String.trim/1)

      _ ->
        []
    end
  end
end
