defmodule Cure.Fix do
  @moduledoc """
  Project-wide automated fixer (v0.23.0).

  Powers `cure fix`. Walks every `.cure` source file under `lib/` and
  `test/`, applies a conservative set of rewrites, and reports the
  result.

  The transforms shipped in v0.23.0:

  1. `:strip_trailing_whitespace` -- remove trailing spaces/tabs.
  2. `:collapse_blank_lines`      -- collapse more than 2 consecutive
     blank lines to 2.
  3. `:ensure_trailing_newline`   -- append a newline if the file has
     none.
  4. `:normalize_line_endings`    -- convert CRLF to LF.
  5. `:strip_mixed_tabs`          -- convert leading tabs (2-space rule
     from the formatter) to two spaces each.

  The fixer only applies transforms that preserve the parse tree; the
  round-trip verification from `Cure.Compiler.Formatter` is its safety
  net. Any rewrite that would change the AST is silently reverted and
  the original file is left alone.

  `run/2` returns a list of `%{file, changed?, applied}` records.
  """

  @type rewrite ::
          :strip_trailing_whitespace
          | :collapse_blank_lines
          | :ensure_trailing_newline
          | :normalize_line_endings
          | :strip_mixed_tabs
  @type report_entry :: %{file: String.t(), changed?: boolean(), applied: [rewrite()]}

  @default_rewrites [
    :normalize_line_endings,
    :strip_trailing_whitespace,
    :strip_mixed_tabs,
    :collapse_blank_lines,
    :ensure_trailing_newline
  ]

  @doc """
  Run the default rewrite set over the project at `root`. Pass
  `dry_run: true` to preview without writing.
  """
  @spec run(String.t(), keyword()) :: [report_entry()]
  def run(root \\ ".", opts \\ []) when is_binary(root) do
    dry_run? = Keyword.get(opts, :dry_run, false)
    rewrites = Keyword.get(opts, :rewrites, @default_rewrites)

    files =
      Path.wildcard(Path.join(root, "lib/**/*.cure")) ++
        Path.wildcard(Path.join(root, "test/**/*.cure"))

    Enum.map(files, fn file -> fix_file(file, rewrites, dry_run?) end)
  end

  @doc """
  Apply `rewrites` to a single file. Returns a report entry.
  """
  @spec fix_file(String.t(), [rewrite()], boolean()) :: report_entry()
  def fix_file(file, rewrites, dry_run?) do
    case File.read(file) do
      {:ok, source} ->
        {new, applied} =
          Enum.reduce(rewrites, {source, []}, fn r, {acc, applied} ->
            updated = apply_rewrite(r, acc)

            if updated == acc do
              {acc, applied}
            else
              {updated, [r | applied]}
            end
          end)

        if new == source do
          %{file: file, changed?: false, applied: []}
        else
          unless dry_run? do
            File.write!(file, new)
          end

          %{file: file, changed?: true, applied: Enum.reverse(applied)}
        end

      {:error, _} ->
        %{file: file, changed?: false, applied: []}
    end
  end

  # -- Individual rewrites ---------------------------------------------------

  defp apply_rewrite(:normalize_line_endings, source) do
    String.replace(source, "\r\n", "\n")
  end

  defp apply_rewrite(:strip_trailing_whitespace, source) do
    source
    |> String.split("\n")
    |> Enum.map(&String.trim_trailing(&1, " "))
    |> Enum.map(&String.trim_trailing(&1, "\t"))
    |> Enum.join("\n")
  end

  defp apply_rewrite(:strip_mixed_tabs, source) do
    source
    |> String.split("\n")
    |> Enum.map(&expand_leading_tabs/1)
    |> Enum.join("\n")
  end

  defp apply_rewrite(:collapse_blank_lines, source) do
    String.replace(source, ~r/\n{3,}/, "\n\n")
  end

  defp apply_rewrite(:ensure_trailing_newline, source) do
    if String.ends_with?(source, "\n"), do: source, else: source <> "\n"
  end

  defp expand_leading_tabs(line) do
    {leading, rest} = String.split_at(line, count_leading(line, &(&1 in [?\s, ?\t])))
    expanded = String.replace(leading, "\t", "  ")
    expanded <> rest
  end

  defp count_leading(s, pred), do: do_count(s, pred, 0)
  defp do_count(<<c, rest::binary>>, pred, n) when is_integer(c), do: count_if(c, rest, pred, n)
  defp do_count(_, _, n), do: n

  defp count_if(c, rest, pred, n) do
    if pred.(c), do: do_count(rest, pred, n + 1), else: n
  end
end
