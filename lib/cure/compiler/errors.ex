defmodule Cure.Compiler.Errors do
  @moduledoc """
  Formats compiler errors into human-readable messages with source locations.

  Handles errors from every pipeline stage: lexer, parser, type checker,
  codegen, and FSM verifier.

  ## Example output

      error: type mismatch in function 'bad'
       --> hello.cure:3
        | declared return type Int but body has type String
  """

  @doc """
  Format a compiler error into a human-readable string.

  Accepts error tuples from any pipeline stage and a file path for context.
  """
  @spec format_error(term(), String.t()) :: String.t()
  def format_error(error, file \\ "nofile")

  # -- Type Errors -------------------------------------------------------------

  def format_error({:type_error, errors}, file) when is_list(errors) do
    Enum.map_join(errors, "\n", &format_error(&1, file))
  end

  def format_error({:type_mismatch, message, meta}, file) do
    line = Keyword.get(meta, :line, 0)
    format_diagnostic("error", "type mismatch", file, line, message)
  end

  def format_error({:unbound_variable, message, meta}, file) do
    line = Keyword.get(meta, :line, 0)
    format_diagnostic("error", "unbound variable", file, line, message)
  end

  def format_error({:arity_mismatch, message, meta}, file) do
    line = Keyword.get(meta, :line, 0)
    format_diagnostic("error", "arity mismatch", file, line, message)
  end

  # -- Parse Errors ------------------------------------------------------------

  def format_error({:parse_error, errors}, file) when is_list(errors) do
    Enum.map_join(errors, "\n", &format_error(&1, file))
  end

  def format_error({:unexpected_token, token_type, line, col}, file) do
    format_diagnostic("error", "unexpected token", file, line, "unexpected #{token_type} at column #{col}")
  end

  def format_error({:expected, expected, :got, got, line, col}, file) do
    format_diagnostic("error", "syntax error", file, line, "expected #{expected}, got #{got} at column #{col}")
  end

  # -- Lex Errors --------------------------------------------------------------

  def format_error({:lex_error, reason}, file) do
    format_diagnostic("error", "lexer error", file, 0, inspect(reason))
  end

  # -- Codegen Errors ----------------------------------------------------------

  def format_error({:codegen_error, reason}, file) do
    format_diagnostic("error", "codegen error", file, 0, inspect(reason))
  end

  def format_error({:expected_module, _ast}, file) do
    format_diagnostic("error", "codegen error", file, 0, "expected a module definition")
  end

  def format_error({:unsupported_container, type}, file) do
    format_diagnostic("error", "codegen error", file, 0, "unsupported container type: #{type}")
  end

  # -- FSM Verifier Errors -----------------------------------------------------

  def format_error({:unreachable_state, message, meta}, file) do
    line = Keyword.get(meta, :line, 0)
    format_diagnostic("error", "unreachable state", file, line, message)
  end

  def format_error({:deadlock, message, meta}, file) do
    line = Keyword.get(meta, :line, 0)
    format_diagnostic("error", "deadlock", file, line, message)
  end

  def format_error({:invalid_terminal, message, meta}, file) do
    line = Keyword.get(meta, :line, 0)
    format_diagnostic("error", "invalid terminal state", file, line, message)
  end

  # -- File Errors -------------------------------------------------------------

  def format_error({:file_read_error, path, reason}, _file) do
    format_diagnostic("error", "file error", path, 0, "cannot read file: #{:file.format_error(reason)}")
  end

  # -- Catch-all ---------------------------------------------------------------

  def format_error(error, file) do
    format_diagnostic("error", "compilation error", file, 0, inspect(error))
  end

  # -- "Did you mean?" Suggestions ---------------------------------------------

  # -- Error Catalog ------------------------------------------------------------

  @error_catalog %{
    "E001" => """
    E001: Type Mismatch

    A function's body type does not match its declared return type,
    or an argument type does not match the parameter type.

    Example:
      fn add(a: Int, b: Int) -> String = a + b
      # Error: declared return type String but body has type Int

    Fix: change the return type annotation or the function body.
    """,
    "E002" => """
    E002: Unbound Variable

    A variable is referenced that has not been defined in the current scope.

    Example:
      fn foo() -> Int = x + 1
      # Error: undefined variable 'x'

    Fix: define the variable with let, or check for typos.
    """,
    "E003" => """
    E003: Arity Mismatch

    A function is called with the wrong number of arguments.

    Example:
      fn add(a: Int, b: Int) -> Int = a + b
      fn main() -> Int = add(1)  # Error: expects 2 arguments, got 1

    Fix: provide the correct number of arguments.
    """,
    "E004" => """
    E004: Non-Exhaustive Match

    A match expression does not cover all possible values of the scrutinee type.

    Example:
      match x
        true -> "yes"
      # Warning: missing pattern for 'false'

    Fix: add the missing patterns or a wildcard (_ -> ...).
    """,
    "E005" => """
    E005: Constraint Violation

    A function with a guard constraint is called with arguments that
    may violate the constraint.

    Example:
      fn safe_div(a: Int, b: Int) -> Int when b != 0 = a / b
      fn main() -> Int = safe_div(10, 0)  # Warning: b != 0 may be violated

    Fix: ensure the arguments satisfy the guard condition.
    """,
    "E006" => """
    E006: Effect Violation

    A function performs an effect that is not declared in its effect
    annotation. Either add the missing effect to the `!` annotation or
    remove the effectful operation.

    Example:
      fn pure_add(a: Int, b: Int) -> Int = println("adding"); a + b
      # Error: undeclared effect Io

    Fix: annotate as `fn pure_add(a: Int, b: Int) -> Int ! Io` or
    remove the println call.
    """,
    "E007" => """
    E007: Unused Variable

    A variable is defined but never referenced. Prefix unused variables
    with `_` to suppress this warning.

    Example:
      fn foo() -> Int =
        let x = 42
        0
      # Warning: unused variable 'x'

    Fix: use the variable or rename it to `_x`.
    """,
    "E008" => """
    E008: Undocumented Public Function

    A public function has no `##` doc comment. This warning is only
    emitted when `cure doc --strict` is used.

    Fix: add a `##` doc comment above the function definition.
    """,
    "E009" => """
    E009: Unreachable Clause

    A pattern matching clause is shadowed by a prior clause and can
    never be reached.

    Example:
      fn classify(x: Int) -> String
        | _ -> "other"
        | 0 -> "zero"   # Unreachable: wildcard above catches everything

    Fix: reorder the clauses so more specific patterns come first.
    """,
    "E010" => """
    E010: Missing Effect Annotation

    A public function performs side effects but has no `!` annotation.
    This warning is only emitted when `--strict-effects` is enabled.

    Fix: add an effect annotation, e.g. `fn greet() -> Atom ! Io`.
    """
  }

  @doc """
  Look up an error code explanation.

  Returns `{:ok, text}` or `:error` if the code is unknown.
  """
  @spec explain(String.t()) :: {:ok, String.t()} | :error
  def explain(code) do
    case Map.get(@error_catalog, String.upcase(code)) do
      nil -> :error
      text -> {:ok, String.trim(text)}
    end
  end

  @doc """
  Suggest similar names for typos using Levenshtein distance.
  """
  @spec suggest(String.t(), [String.t()]) :: String.t() | nil
  def suggest(name, candidates) do
    candidates
    |> Enum.map(fn c -> {c, levenshtein(name, c)} end)
    |> Enum.filter(fn {_, d} -> d > 0 and d <= 2 end)
    |> Enum.sort_by(fn {_, d} -> d end)
    |> case do
      [{best, _} | _] -> best
      _ -> nil
    end
  end

  @doc """
  Format an error with source context showing the offending line.
  """
  @spec format_with_source(term(), String.t(), String.t()) :: String.t()
  def format_with_source(error, file, source) do
    base = format_error(error, file)
    line_num = extract_line(error)

    if line_num > 0 and source != "" do
      lines = String.split(source, "\n")

      case Enum.at(lines, line_num - 1) do
        nil ->
          base

        src_line ->
          col = extract_col(error)
          caret = if col > 0, do: "\n      | #{String.duplicate(" ", col - 1)}^", else: ""
          base <> "\n      | #{src_line}" <> caret
      end
    else
      base
    end
  end

  # -- Formatting Helper -------------------------------------------------------

  defp format_diagnostic(severity, category, file, line, message) do
    location =
      if line > 0 do
        " --> #{file}:#{line}"
      else
        " --> #{file}"
      end

    """
    #{severity}: #{category}
    #{location}
      | #{message}\
    """
    |> String.trim_trailing()
  end

  defp extract_line({_, _, meta}) when is_list(meta), do: Keyword.get(meta, :line, 0)
  defp extract_line({_, _, line, _col}) when is_integer(line), do: line
  defp extract_line(_), do: 0

  defp extract_col({_, _, _line, col}) when is_integer(col), do: col
  defp extract_col(_), do: 0

  # Levenshtein distance for typo suggestions
  defp levenshtein(s, t) do
    s_len = String.length(s)
    t_len = String.length(t)
    s_chars = String.graphemes(s)
    t_chars = String.graphemes(t)

    if s_len == 0 do
      t_len
    else
      if t_len == 0 do
        s_len
      else
        prev_row = Enum.to_list(0..t_len)

        Enum.reduce(Enum.with_index(s_chars, 1), prev_row, fn {s_ch, i}, row ->
          first = [i]

          rest =
            Enum.reduce(Enum.with_index(t_chars, 1), {first, row}, fn {t_ch, j}, {new_row, old_row} ->
              cost = if s_ch == t_ch, do: 0, else: 1

              val =
                Enum.min([
                  Enum.at(old_row, j) + 1,
                  List.last(new_row) + 1,
                  Enum.at(old_row, j - 1) + cost
                ])

              {new_row ++ [val], old_row}
            end)

          elem(rest, 0)
        end)
        |> List.last()
      end
    end
  end
end
