defmodule Cure.REPL.Markdown do
  @moduledoc """
  Minimal, dependency-free Markdown-to-ANSI renderer used for `:help`
  and `:doc` output.

  Marcli (the richer renderer) routes through MDEx's Rust NIF, which
  cannot be loaded from inside an escript archive -- the NIF lives in
  `priv/native/*.so` and the escript bundles everything into a single
  file, so the dynamic loader sees a path like `/.../cure/mdex/priv/...`
  that doesn't exist on disk. This module therefore implements a small
  block-aware Markdown renderer targeting ANSI, with colours drawn
  from the provided `Cure.REPL.Theme`. It covers:

    * ATX headings (`#`, `##`, `###`)
    * Fenced code blocks (` ```lang ` ... ` ``` `) and indented code
      blocks (four-space or tab indent)
    * Bullet lists starting with `- ` or `* ` and numbered lists
      (`1.`, `2.`, ...)
    * Blockquotes (`> `)
    * Inline backtick code: `` `code` ``
    * Inline bold (`**bold**`) and italic (`*italic*`)
    * Inline links `[text](url)` -- rendered as `text (url)`
    * Horizontal rules (`---` or `***`)
    * Blank-line paragraph separation (preserved)
  """

  alias Cure.REPL.Theme

  @doc "Render `markdown` as ANSI text using `theme`."
  @spec render(String.t(), Theme.t()) :: String.t()
  def render(markdown, %Theme{} = theme) when is_binary(markdown) do
    markdown
    |> String.split("\n")
    |> render_blocks(theme, [])
    |> Enum.reverse()
    |> Enum.join("\n")
  end

  # -- Block loop -------------------------------------------------------------
  #
  # Walks the source line-by-line, detecting the entry point of a
  # block (fenced code, indented code, everything else) and handing
  # off to a sub-routine that consumes until the block ends. Lines
  # that are not part of a block are rendered through `render_line/2`
  # so inline styling still applies.

  defp render_blocks([], _theme, acc), do: acc

  defp render_blocks([line | rest], theme, acc) do
    cond do
      fenced_code_start?(line) ->
        {lang, rest_after_fence} = start_fence(line, rest)
        {block_lines, tail} = take_until_fence(rest_after_fence, [])
        rendered = render_fenced_code(block_lines, lang, theme)
        render_blocks(tail, theme, [rendered | acc])

      true ->
        render_blocks(rest, theme, [render_line(line, theme) | acc])
    end
  end

  defp fenced_code_start?("```" <> _), do: true
  defp fenced_code_start?(_), do: false

  defp start_fence("```" <> rest, tail), do: {String.trim(rest), tail}

  defp take_until_fence([], acc), do: {Enum.reverse(acc), []}

  defp take_until_fence([line | rest], acc) do
    cond do
      String.starts_with?(line, "```") -> {Enum.reverse(acc), rest}
      true -> take_until_fence(rest, [line | acc])
    end
  end

  defp render_fenced_code(lines, _lang, theme) do
    body = Enum.join(lines, "\n")
    rule = theme.dim <> "\u2502 " <> theme.reset

    highlighted_lines =
      body
      |> String.split("\n")
      |> Enum.map(&(rule <> theme.match <> &1 <> theme.reset))

    Enum.join(highlighted_lines, "\n")
  end

  # -- Line dispatch ---------------------------------------------------------

  defp render_line("# " <> rest, theme),
    do: bold(theme) <> yellow(theme) <> rest <> theme.reset

  defp render_line("## " <> rest, theme),
    do: bold(theme) <> cyan(theme) <> rest <> theme.reset

  defp render_line("### " <> rest, theme),
    do: bold(theme) <> rest <> theme.reset

  defp render_line("---", theme),
    do: theme.dim <> String.duplicate("-", 40) <> theme.reset

  defp render_line("***", theme),
    do: theme.dim <> String.duplicate("-", 40) <> theme.reset

  defp render_line("- " <> rest, theme),
    do: "  " <> theme.result_arrow <> "\u2022" <> theme.reset <> " " <> render_inline(rest, theme)

  defp render_line("* " <> rest, theme),
    do: "  " <> theme.result_arrow <> "\u2022" <> theme.reset <> " " <> render_inline(rest, theme)

  defp render_line("> " <> rest, theme),
    do: theme.dim <> "\u2502 " <> theme.reset <> render_inline(rest, theme)

  defp render_line("    " <> rest, theme),
    do: theme.dim <> "\u2502 " <> theme.reset <> theme.match <> rest <> theme.reset

  defp render_line("\t" <> rest, theme),
    do: theme.dim <> "\u2502 " <> theme.reset <> theme.match <> rest <> theme.reset

  defp render_line(line, theme) do
    case Regex.run(~r/^(\s*)(\d+)\.\s+(.*)$/, line) do
      [_, indent, num, rest] ->
        indent <>
          theme.result_arrow <>
          num <> "." <> theme.reset <> " " <> render_inline(rest, theme)

      _ ->
        render_inline(line, theme)
    end
  end

  # -- Inline processing ----------------------------------------------------

  defp render_inline(text, theme), do: inline(text, theme, <<>>)

  defp inline(<<>>, _theme, acc), do: acc

  defp inline(<<"[", rest::binary>>, theme, acc) do
    case Regex.run(~r/^([^\]]*)\]\(([^)]+)\)(.*)$/s, rest) do
      [_, text, url, tail] ->
        styled =
          theme.match <> text <> theme.reset <> theme.dim <> " (" <> url <> ")" <> theme.reset

        inline(tail, theme, acc <> styled)

      _ ->
        inline(rest, theme, acc <> "[")
    end
  end

  defp inline(<<"`", rest::binary>>, theme, acc) do
    case :binary.split(rest, "`") do
      [code, tail] ->
        inline(tail, theme, acc <> theme.match <> code <> theme.reset)

      [_] ->
        inline(rest, theme, acc <> "`")
    end
  end

  defp inline(<<"**", rest::binary>>, theme, acc) do
    case :binary.split(rest, "**") do
      [body, tail] ->
        inline(tail, theme, acc <> bold(theme) <> body <> theme.reset)

      [_] ->
        inline(rest, theme, acc <> "**")
    end
  end

  defp inline(<<"*", rest::binary>>, theme, acc) do
    case :binary.split(rest, "*") do
      [body, tail] ->
        inline(tail, theme, acc <> italic(theme) <> body <> theme.reset)

      [_] ->
        inline(rest, theme, acc <> "*")
    end
  end

  defp inline(<<c::utf8, rest::binary>>, theme, acc),
    do: inline(rest, theme, acc <> <<c::utf8>>)

  # -- Style builders -------------------------------------------------------

  defp bold(%Theme{name: :mono}), do: ""
  defp bold(_), do: "\e[1m"

  defp italic(%Theme{name: :mono}), do: ""
  defp italic(_), do: "\e[3m"

  defp cyan(%Theme{name: :mono}), do: ""
  defp cyan(_), do: "\e[36m"

  defp yellow(%Theme{name: :mono}), do: ""
  defp yellow(_), do: "\e[33m"
end
