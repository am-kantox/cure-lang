defmodule Cure.REPL.Markdown do
  @moduledoc """
  Minimal, dependency-free Markdown-to-ANSI renderer used for `:help`
  output.

  Marcli (the richer renderer) routes through MDEx's Rust NIF, which
  cannot be loaded from inside an escript archive -- the NIF lives in
  `priv/native/*.so` and the escript bundles everything into a single
  file, so the dynamic loader sees a path like `/.../cure/mdex/priv/...`
  that doesn't exist on disk. This module covers just the subset of
  Markdown the REPL `:help` payload uses:

    * ATX headings (`#`, `##`, `###`)
    * Bullet lists starting with `- `
    * Inline backtick code: `` `code` ``
    * Inline bold (`**bold**`) and italic (`*italic*`)
    * Horizontal rules (`---`)
    * Blank-line paragraph separation

  Output is plain ANSI with colours drawn from the provided
  `Cure.REPL.Theme`.
  """

  alias Cure.REPL.Theme

  @doc "Render `markdown` as ANSI text using `theme`."
  @spec render(String.t(), Theme.t()) :: String.t()
  def render(markdown, %Theme{} = theme) when is_binary(markdown) do
    markdown
    |> String.split("\n")
    |> Enum.map_join("\n", &render_line(&1, theme))
  end

  defp render_line("# " <> rest, theme),
    do: bold(theme) <> yellow(theme) <> rest <> theme.reset

  defp render_line("## " <> rest, theme),
    do: bold(theme) <> cyan(theme) <> rest <> theme.reset

  defp render_line("### " <> rest, theme),
    do: bold(theme) <> rest <> theme.reset

  defp render_line("---", theme),
    do: theme.dim <> String.duplicate("-", 40) <> theme.reset

  defp render_line("- " <> rest, theme),
    do: "  " <> theme.result_arrow <> "•" <> theme.reset <> " " <> render_inline(rest, theme)

  defp render_line(other, theme), do: render_inline(other, theme)

  # Inline processing: walk a string, swapping `` `code` ``, `**bold**`
  # and `*italic*` segments for their ANSI-styled equivalents.
  defp render_inline(text, theme), do: inline(text, theme, <<>>)

  defp inline(<<>>, _theme, acc), do: acc

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
