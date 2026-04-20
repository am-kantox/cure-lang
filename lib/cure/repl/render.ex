defmodule Cure.REPL.Render do
  @moduledoc """
  Redraw the current line + prompt, with cursor placement, on every
  editor transition. Uses ANSI sequences to overwrite the current
  terminal row instead of appending scroll output.

  All output goes through `IO.binwrite(:stdio, ...)` so ANSI escapes
  don't get re-encoded. The module is otherwise state-less; it receives
  the REPL snapshot it needs as arguments.
  """

  alias Cure.REPL.{Highlight, LineEditor, Terminal, Theme}

  # Clear the current line and return to column 0.
  @clear_line "\r\e[2K"
  # Clear from cursor to end of screen (used after showing completion hints).
  @clear_below "\e[J"

  @doc "Build the primary prompt string, coloured via `theme`."
  @spec prompt(non_neg_integer(), Theme.t(), LineEditor.mode()) :: String.t()
  def prompt(n, %Theme{} = theme, mode \\ :emacs) do
    mode_badge =
      case mode do
        :vi_normal -> theme.warn <> "[N] " <> theme.reset
        :vi_insert -> theme.ok <> "[I] " <> theme.reset
        _ -> ""
      end

    mode_badge <>
      theme.prompt <>
      "cure(" <>
      theme.reset <>
      theme.prompt_n <>
      Integer.to_string(n) <>
      theme.reset <>
      theme.prompt <>
      ")> " <>
      theme.reset
  end

  @doc "Build the continuation prompt (indented to primary prompt width)."
  @spec continuation(non_neg_integer(), Theme.t()) :: String.t()
  def continuation(n, %Theme{} = theme) do
    # Match the printable width of the primary prompt "cure(N)> ".
    pad = String.duplicate(" ", String.length("cure(#{n})> ") - 4)
    theme.prompt_cont <> pad <> "... " <> theme.reset
  end

  @doc """
  Redraw the buffer line. Clears the current row, writes the coloured
  prompt + highlighted buffer, then moves the cursor back to the logical
  grapheme position.
  """
  @spec redraw(LineEditor.t(), non_neg_integer(), Theme.t(), keyword()) :: :ok
  def redraw(%LineEditor{} = ed, n, %Theme{} = theme, opts \\ []) do
    prompt = Keyword.get(opts, :prompt, prompt(n, theme, ed.mode))
    prompt_width = ansi_length(prompt)

    highlighted =
      if theme.name == :mono do
        ed.buffer
      else
        Highlight.highlight(ed.buffer)
      end

    output = [
      @clear_line,
      prompt,
      highlighted,
      move_cursor_to_column(prompt_width + ed.cursor)
    ]

    Terminal.write(IO.iodata_to_binary(output))
    :ok
  end

  @doc """
  Redraw a status line below the prompt (for Ctrl+R incremental search).
  Returns the cursor to the main input row afterwards.
  """
  @spec draw_search_status(String.t(), Theme.t()) :: :ok
  def draw_search_status(status, %Theme{} = theme) do
    # Save cursor, move to next row, clear it, write status, restore cursor.
    output = [
      "\e7",
      "\n",
      @clear_line,
      theme.status,
      status,
      theme.reset,
      "\e8"
    ]

    Terminal.write(IO.iodata_to_binary(output))
    :ok
  end

  @doc "Clear any helper rows drawn below the input (completions, search)."
  @spec clear_helpers() :: :ok
  def clear_helpers do
    Terminal.write(["\e7", "\n", @clear_line, "\e8"])
    :ok
  end

  @doc """
  Write a line through the terminal, translating every `\n` inside
  `text` into `\r\n` so raw-mode terminals return to column 0 between
  lines. (In raw mode the tty's `ONLCR` output processing is commonly
  disabled, so a bare `\n` moves the cursor down without going back to
  the start of the row.)
  """
  @spec write_line(String.t()) :: :ok
  def write_line(text) do
    Terminal.write([normalize(text), "\r\n"])
    :ok
  end

  @doc "Drop down one row and clear whatever helper lines exist below."
  @spec newline() :: :ok
  def newline do
    Terminal.write(["\r\n", @clear_below])
    :ok
  end

  # Replace every standalone LF with CRLF so raw-mode terminals return to
  # column 0 between lines. Existing CRLFs are preserved verbatim.
  defp normalize(text) when is_binary(text) do
    text
    |> String.replace("\r\n", "\n")
    |> String.replace("\n", "\r\n")
  end

  @doc "Clear the full screen (Ctrl+L)."
  @spec clear_screen() :: :ok
  def clear_screen do
    Terminal.write("\e[H\e[2J")
    :ok
  end

  @doc "Visible width of a string, counting graphemes and skipping ANSI escapes."
  @spec ansi_length(String.t()) :: non_neg_integer()
  def ansi_length(text) do
    text
    |> Theme.strip_ansi()
    |> String.length()
  end

  # Move cursor to absolute column on the current row (1-based).
  defp move_cursor_to_column(col) when col >= 0, do: "\r\e[#{col}C"
end
