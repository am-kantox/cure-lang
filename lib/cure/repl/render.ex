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

  `cursor_col` is the absolute column (1-based, counted in printable
  graphemes) the caller wants the cursor restored to on the prompt row.
  It is typically `ansi_length(prompt) + editor.cursor`.

  The implementation uses only **relative** cursor motion. `\e7` /
  `\e8` (DECSC/DECRC) save and restore an absolute screen coordinate:
  if writing the descent `\n` scrolls the viewport (cursor was on the
  last row), the saved coordinate would point one line below the
  prompt after the scroll. `\e[1A` goes up one *physical* row, which
  is always the prompt row regardless of whether the descent scrolled.
  """
  @spec draw_search_status(String.t(), Theme.t(), non_neg_integer()) :: :ok
  def draw_search_status(status, %Theme{} = theme, cursor_col)
      when is_integer(cursor_col) and cursor_col >= 0 do
    Terminal.write(IO.iodata_to_binary(encode_search_status(status, theme, cursor_col)))
    :ok
  end

  @doc false
  # Pure iodata builder for `draw_search_status/3`, exposed for tests.
  @spec encode_search_status(String.t(), Theme.t(), non_neg_integer()) :: iodata()
  def encode_search_status(status, %Theme{} = theme, cursor_col)
      when is_integer(cursor_col) and cursor_col >= 0 do
    [
      "\r\n",
      @clear_line,
      theme.status,
      status,
      theme.reset,
      "\e[1A",
      move_cursor_to_column(cursor_col)
    ]
  end

  @doc """
  Clear any helper rows drawn below the input (completions, search)
  and return the cursor to `cursor_col` on the prompt row.

  Mirrors `draw_search_status/3`: relative motion only, so a descent
  that scrolls the viewport still ascends back to the prompt row.
  """
  @spec clear_helpers(non_neg_integer()) :: :ok
  def clear_helpers(cursor_col \\ 0)
      when is_integer(cursor_col) and cursor_col >= 0 do
    Terminal.write(IO.iodata_to_binary(encode_clear_helpers(cursor_col)))
    :ok
  end

  @doc false
  # Pure iodata builder for `clear_helpers/1`, exposed for tests.
  @spec encode_clear_helpers(non_neg_integer()) :: iodata()
  def encode_clear_helpers(cursor_col)
      when is_integer(cursor_col) and cursor_col >= 0 do
    ["\r\n", @clear_line, "\e[1A", move_cursor_to_column(cursor_col)]
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

  # Move cursor to column `col` on the current row.
  #
  # `\e[0C` (CUF with an explicit zero) is defined by ECMA-48 as a
  # one-column move on common terminals (xterm, iTerm2, Linux console),
  # which would leave the cursor off by one. We therefore emit just
  # `\r` for `col == 0` and the full escape only when it is meaningful.
  @doc false
  @spec move_cursor_to_column(non_neg_integer()) :: iodata()
  def move_cursor_to_column(0), do: "\r"
  def move_cursor_to_column(col) when is_integer(col) and col > 0, do: "\r\e[#{col}C"
end
