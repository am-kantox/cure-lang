defmodule Cure.Bless do
  @moduledoc """
  Socratic type-error assistant (`cure bless`).

  Reads a failing type or refinement diagnostic, walks the user
  through fixing it interactively:

  1. Parse the structured error tuple.
  2. Delegate to `Cure.Bless.Advisor` to produce a human-readable
     explanation and a ranked list of concrete fix suggestions.
  3. Present the top suggestion with a `[y/n/s(kip)]` prompt.
  4. On `y`, apply the fix to the source file and re-run the checker
     to confirm the error is resolved.

  ## CLI surface

      cure bless path/to/file.cure

  ## REPL surface

      cure(1)> :bless path/to/file.cure

  Re-running `:bless` without an argument re-processes the same file
  from the REPL state.
  """

  alias Cure.Bless.Advisor
  alias Cure.Compiler.Errors

  @type error_tuple :: {atom(), String.t(), keyword()}
  @type session_result :: :all_fixed | :some_skipped | :nothing_to_fix | {:error, String.t()}

  # -- Public API --------------------------------------------------------------

  @doc """
  Interactive bless session for a single `.cure` file.

  Compiles the file, collects every type error, and walks the user
  through each one in order. Returns a summary atom describing the
  overall outcome of the session.
  """
  @spec bless_file(String.t(), keyword()) :: session_result()
  def bless_file(path, opts \\ []) do
    case File.read(path) do
      {:error, reason} ->
        {:error, "cannot read #{path}: #{:file.format_error(reason)}"}

      {:ok, source} ->
        errors = collect_errors(source, path)
        bless_errors(errors, source, path, opts)
    end
  end

  @doc """
  Non-interactive: return a list of `{error, [suggestion]}` pairs for
  a source string. Used by the LSP and tests.
  """
  @spec advise(String.t(), String.t()) :: [{error_tuple(), [Advisor.suggestion()]}]
  def advise(source, path \\ "nofile") do
    errors = collect_errors(source, path)
    Enum.map(errors, fn err -> {err, Advisor.suggest(err, source)} end)
  end

  # -- Error collection --------------------------------------------------------

  defp collect_errors(source, path) do
    with {:ok, tokens} <-
           Cure.Compiler.Lexer.tokenize(source, file: path, emit_events: false),
         {:ok, ast} <-
           Cure.Compiler.Parser.parse(tokens, file: path, emit_events: false),
         {:error, errors} <-
           Cure.Types.Checker.check_module(ast,
             file: path,
             emit_events: false
           ) do
      errors
    else
      # Source parsed and type-checked cleanly.
      {:ok, _} -> []
      # Lex / parse errors are not in scope for bless.
      {:error, _} -> []
    end
  end

  # -- Interactive session -----------------------------------------------------

  defp bless_errors([], _source, _path, _opts) do
    :nothing_to_fix
  end

  defp bless_errors(errors, source, path, opts) do
    interactive? = Keyword.get(opts, :interactive, true)

    {fixed, skipped} =
      Enum.reduce(errors, {0, 0}, fn err, {f, s} ->
        suggestions = Advisor.suggest(err, source)

        case suggestions do
          [] ->
            print_error(err, path)
            IO.puts("  (no automatic fix available)\n")
            {f, s + 1}

          [top | _rest] ->
            print_error(err, path)
            print_suggestion(top)

            if interactive? do
              case prompt_user() do
                :apply ->
                  case apply_fix(top, source, path) do
                    {:ok, new_source} ->
                      File.write!(path, new_source)
                      IO.puts("  Applied. Re-checking...")

                      case collect_errors(new_source, path) do
                        [] -> IO.puts("  No more errors.\n")
                        remaining -> IO.puts("  #{length(remaining)} error(s) remain.\n")
                      end

                      {f + 1, s}

                    {:error, reason} ->
                      IO.puts("  Could not apply fix: #{reason}\n")
                      {f, s + 1}
                  end

                :skip ->
                  IO.puts("  Skipped.\n")
                  {f, s + 1}

                :no ->
                  IO.puts("  Declined.\n")
                  {f, s + 1}
              end
            else
              {f, s + 1}
            end
        end
      end)

    cond do
      skipped == 0 -> :all_fixed
      fixed == 0 -> :some_skipped
      true -> :some_skipped
    end
  end

  # -- Rendering ---------------------------------------------------------------

  defp print_error(err, file) do
    IO.puts("\n" <> Errors.format_error(err, file))
  end

  defp print_suggestion(%{kind: kind, description: desc, patch: _}) do
    IO.puts("  Suggestion (#{kind}): #{desc}")
  end

  defp prompt_user do
    IO.write("  Apply? [y]es / [n]o / [s]kip: ")

    case IO.gets("") do
      :eof -> :no
      input -> parse_prompt(String.trim(String.downcase(input)))
    end
  end

  defp parse_prompt("y"), do: :apply
  defp parse_prompt("yes"), do: :apply
  defp parse_prompt("s"), do: :skip
  defp parse_prompt("skip"), do: :skip
  defp parse_prompt(_), do: :no

  # -- Fix application ---------------------------------------------------------

  defp apply_fix(%{patch: patch}, source, _path) when is_function(patch, 1) do
    case patch.(source) do
      {:ok, new_source} when is_binary(new_source) -> {:ok, new_source}
      {:error, _} = err -> err
      other -> {:error, "unexpected patch result: #{inspect(other)}"}
    end
  end

  defp apply_fix(%{patch: nil}, _source, _path) do
    {:error, "no patch function provided"}
  end

  defp apply_fix(_suggestion, _source, _path) do
    {:error, "malformed suggestion"}
  end
end
