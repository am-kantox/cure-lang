defmodule Cure.REPL.LineEditor do
  @moduledoc """
  Pure-function line editor driving the interactive REPL.

  A `LineEditor` holds the current input buffer, the cursor position
  (as a 0-based grapheme index), a bounded kill ring, and undo/redo
  stacks. All editing operations are pure functions over the struct so
  the module is trivially unit-testable without a tty.

  Both the Emacs and a minimal Vi key-binding schemes are supported;
  the driver translates raw key events from `Cure.REPL.Terminal` into
  `handle/2` calls.
  """

  alias __MODULE__, as: LE

  @kill_ring_size 10
  @undo_depth 100

  defstruct buffer: "",
            cursor: 0,
            kill_ring: [],
            mode: :emacs,
            undo: [],
            redo: []

  @type mode :: :emacs | :vi_insert | :vi_normal
  @type t :: %LE{
          buffer: String.t(),
          cursor: non_neg_integer(),
          kill_ring: [String.t()],
          mode: mode(),
          undo: [{String.t(), non_neg_integer()}],
          redo: [{String.t(), non_neg_integer()}]
        }

  @type event ::
          Cure.REPL.Terminal.key()
          | :submit
          | :abort
          | :cancel
          | :eof
          | :noop

  @doc "Create a fresh editor."
  @spec new(keyword()) :: t()
  def new(opts \\ []) do
    %LE{
      buffer: Keyword.get(opts, :buffer, ""),
      cursor: 0,
      mode: Keyword.get(opts, :mode, :emacs)
    }
    |> move_end()
  end

  @doc "Replace the current buffer in-place (used by history navigation)."
  @spec set_buffer(t(), String.t()) :: t()
  def set_buffer(%LE{} = ed, text) when is_binary(text) do
    %{ed | buffer: text, cursor: String.length(text)}
  end

  @doc "Clear the buffer (used on abort)."
  @spec reset(t()) :: t()
  def reset(%LE{} = ed), do: %{ed | buffer: "", cursor: 0, undo: [], redo: []}

  @doc """
  Handle a decoded keypress, returning either an updated editor or a
  control signal.
  """
  @spec handle(t(), Cure.REPL.Terminal.key()) :: {:cont, t()} | {:signal, event(), t()}
  def handle(%LE{mode: :vi_normal} = ed, key), do: handle_vi_normal(ed, key)
  def handle(%LE{} = ed, key), do: handle_emacs(ed, key)

  # -- Emacs / default bindings ---------------------------------------------

  defp handle_emacs(ed, key) do
    case key do
      :enter -> {:signal, :submit, ed}
      :eof -> signal_eof(ed)
      {:ctrl, ?D} -> signal_eof(ed)
      {:ctrl, ?C} -> {:signal, :abort, reset(ed)}
      {:ctrl, ?G} -> {:signal, :cancel, ed}
      :left -> cont(move_left(ed))
      :right -> cont(move_right(ed))
      {:ctrl, ?B} -> cont(move_left(ed))
      {:ctrl, ?F} -> cont(move_right(ed))
      :home -> cont(move_home(ed))
      :end -> cont(move_end(ed))
      {:ctrl, ?A} -> cont(move_home(ed))
      {:ctrl, ?E} -> cont(move_end(ed))
      :word_left -> cont(move_word_left(ed))
      :word_right -> cont(move_word_right(ed))
      {:alt, "b"} -> cont(move_word_left(ed))
      {:alt, "f"} -> cont(move_word_right(ed))
      :backspace -> cont(backspace(ed))
      {:ctrl, ?H} -> cont(backspace(ed))
      :delete -> cont(delete_char(ed))
      {:ctrl, ?K} -> cont(kill_to_end(ed))
      {:ctrl, ?U} -> cont(kill_to_start(ed))
      {:ctrl, ?W} -> cont(kill_word_back(ed))
      {:alt, "d"} -> cont(kill_word_forward(ed))
      {:ctrl, ?Y} -> cont(yank(ed))
      {:alt, "y"} -> cont(yank_rotate(ed))
      {:ctrl, ?T} -> cont(transpose_chars(ed))
      {:alt, "t"} -> cont(transpose_words(ed))
      {:alt, "u"} -> cont(change_word(ed, &String.upcase/1))
      {:alt, "l"} -> cont(change_word(ed, &String.downcase/1))
      {:alt, "c"} -> cont(change_word(ed, &capitalize/1))
      {:ctrl, 31} -> cont(undo(ed))
      {:alt, "_"} -> cont(redo(ed))
      {:key, ch} -> cont(insert(ed, ch))
      {:paste, chunk} -> cont(insert(ed, chunk))
      :esc -> cont(%{ed | mode: toggle_vi(ed.mode, :vi_normal)})
      _ -> cont(ed)
    end
  end

  # -- Minimal vi normal mode -----------------------------------------------

  defp handle_vi_normal(ed, key) do
    case key do
      :enter -> {:signal, :submit, ed}
      {:ctrl, ?C} -> {:signal, :abort, reset(ed)}
      :esc -> cont(ed)
      {:key, "i"} -> cont(%{ed | mode: :vi_insert})
      {:key, "a"} -> cont(%{move_right(ed) | mode: :vi_insert})
      {:key, "I"} -> cont(%{move_home(ed) | mode: :vi_insert})
      {:key, "A"} -> cont(%{move_end(ed) | mode: :vi_insert})
      {:key, "h"} -> cont(move_left(ed))
      {:key, "l"} -> cont(move_right(ed))
      {:key, "0"} -> cont(move_home(ed))
      {:key, "^"} -> cont(move_home(ed))
      {:key, "$"} -> cont(move_end(ed))
      {:key, "w"} -> cont(move_word_right(ed))
      {:key, "b"} -> cont(move_word_left(ed))
      {:key, "e"} -> cont(move_word_right(ed))
      {:key, "x"} -> cont(delete_char(ed))
      {:key, "D"} -> cont(kill_to_end(ed))
      {:key, "C"} -> cont(%{kill_to_end(ed) | mode: :vi_insert})
      {:key, "u"} -> cont(undo(ed))
      {:ctrl, ?R} -> cont(redo(ed))
      _ -> cont(ed)
    end
  end

  defp toggle_vi(:emacs, _), do: :emacs
  defp toggle_vi(:vi_insert, :vi_normal), do: :vi_normal
  defp toggle_vi(other, _), do: other

  defp cont(%LE{} = ed), do: {:cont, ed}
  defp signal_eof(%LE{buffer: ""} = ed), do: {:signal, :eof, ed}
  defp signal_eof(%LE{} = ed), do: cont(delete_char(ed))

  # -- Cursor movement -------------------------------------------------------

  @doc "Move cursor one grapheme to the left."
  @spec move_left(t()) :: t()
  def move_left(%LE{cursor: 0} = ed), do: ed
  def move_left(%LE{cursor: c} = ed), do: %{ed | cursor: c - 1}

  @doc "Move cursor one grapheme to the right."
  @spec move_right(t()) :: t()
  def move_right(%LE{buffer: b, cursor: c} = ed) do
    if c >= String.length(b), do: ed, else: %{ed | cursor: c + 1}
  end

  @doc "Jump cursor to the start of the line."
  @spec move_home(t()) :: t()
  def move_home(%LE{} = ed), do: %{ed | cursor: 0}

  @doc "Jump cursor to the end of the line."
  @spec move_end(t()) :: t()
  def move_end(%LE{buffer: b} = ed), do: %{ed | cursor: String.length(b)}

  @doc "Move cursor to the start of the previous word."
  @spec move_word_left(t()) :: t()
  def move_word_left(%LE{cursor: 0} = ed), do: ed

  def move_word_left(%LE{buffer: b, cursor: c} = ed) do
    graphemes = String.graphemes(b)
    left = Enum.take(graphemes, c)
    new_idx = prev_word_index(left)
    %{ed | cursor: new_idx}
  end

  @doc "Move cursor to the start of the next word."
  @spec move_word_right(t()) :: t()
  def move_word_right(%LE{buffer: b, cursor: c} = ed) do
    graphemes = String.graphemes(b)
    len = length(graphemes)

    if c >= len do
      ed
    else
      right = Enum.drop(graphemes, c)
      offset = next_word_offset(right)
      %{ed | cursor: min(len, c + offset)}
    end
  end

  # -- Text editing ---------------------------------------------------------

  @doc "Insert text at the cursor and advance by its grapheme length."
  @spec insert(t(), String.t()) :: t()
  def insert(%LE{} = ed, text) when is_binary(text) do
    ed = snapshot(ed)
    {l, r} = split(ed)
    new_buf = l <> text <> r
    %{ed | buffer: new_buf, cursor: ed.cursor + String.length(text), redo: []}
  end

  @doc "Remove the grapheme to the left of the cursor."
  @spec backspace(t()) :: t()
  def backspace(%LE{cursor: 0} = ed), do: ed

  def backspace(%LE{} = ed) do
    ed = snapshot(ed)
    {l, r} = split(ed)
    new_l = String.slice(l, 0, String.length(l) - 1)
    %{ed | buffer: new_l <> r, cursor: ed.cursor - 1, redo: []}
  end

  @doc "Remove the grapheme under the cursor."
  @spec delete_char(t()) :: t()
  def delete_char(%LE{} = ed) do
    {l, r} = split(ed)

    if r == "" do
      ed
    else
      ed = snapshot(ed)
      # `String.slice/2` with a stepped range always returns a binary;
      # the historical `|| ""` fallback would never be taken.
      new_r = String.slice(r, 1..-1//1)
      %{ed | buffer: l <> new_r, redo: []}
    end
  end

  @doc "Kill from cursor to end of line; push the removed text onto the kill ring."
  @spec kill_to_end(t()) :: t()
  def kill_to_end(%LE{} = ed) do
    {l, r} = split(ed)

    if r == "" do
      ed
    else
      ed = snapshot(ed)
      %{ed | buffer: l, kill_ring: push_kill(ed.kill_ring, r), redo: []}
    end
  end

  @doc "Kill from start of line to cursor."
  @spec kill_to_start(t()) :: t()
  def kill_to_start(%LE{cursor: 0} = ed), do: ed

  def kill_to_start(%LE{} = ed) do
    ed = snapshot(ed)
    {l, r} = split(ed)
    %{ed | buffer: r, cursor: 0, kill_ring: push_kill(ed.kill_ring, l), redo: []}
  end

  @doc "Kill the word to the left of the cursor."
  @spec kill_word_back(t()) :: t()
  def kill_word_back(%LE{cursor: 0} = ed), do: ed

  def kill_word_back(%LE{} = ed) do
    graphemes = String.graphemes(ed.buffer)
    left = Enum.take(graphemes, ed.cursor)
    right = Enum.drop(graphemes, ed.cursor)
    start = prev_word_index(left)
    killed = left |> Enum.drop(start) |> Enum.join()
    kept_left = left |> Enum.take(start) |> Enum.join()
    ed = snapshot(ed)

    %{
      ed
      | buffer: kept_left <> Enum.join(right),
        cursor: start,
        kill_ring: push_kill(ed.kill_ring, killed),
        redo: []
    }
  end

  @doc "Kill the word to the right of the cursor."
  @spec kill_word_forward(t()) :: t()
  def kill_word_forward(%LE{} = ed) do
    graphemes = String.graphemes(ed.buffer)
    left = Enum.take(graphemes, ed.cursor)
    right = Enum.drop(graphemes, ed.cursor)

    if right == [] do
      ed
    else
      offset = next_word_offset(right)
      killed = right |> Enum.take(offset) |> Enum.join()
      kept_right = right |> Enum.drop(offset) |> Enum.join()
      ed = snapshot(ed)

      %{
        ed
        | buffer: Enum.join(left) <> kept_right,
          kill_ring: push_kill(ed.kill_ring, killed),
          redo: []
      }
    end
  end

  @doc "Yank the most-recent killed text at the cursor."
  @spec yank(t()) :: t()
  def yank(%LE{kill_ring: []} = ed), do: ed
  def yank(%LE{kill_ring: [h | _]} = ed), do: insert(ed, h)

  @doc "Rotate the kill ring; meant to be called after `yank/1`."
  @spec yank_rotate(t()) :: t()
  def yank_rotate(%LE{kill_ring: []} = ed), do: ed
  def yank_rotate(%LE{kill_ring: [h | t]} = ed), do: %{ed | kill_ring: t ++ [h]}

  @doc "Transpose the two characters around the cursor."
  @spec transpose_chars(t()) :: t()
  def transpose_chars(%LE{cursor: 0} = ed), do: ed

  def transpose_chars(%LE{} = ed) do
    graphemes = String.graphemes(ed.buffer)
    len = length(graphemes)

    if len < 2 do
      ed
    else
      ed = snapshot(ed)
      c = min(ed.cursor, len)

      {i, j, new_cursor} =
        cond do
          c == len -> {c - 2, c - 1, c}
          true -> {c - 1, c, c + 1}
        end

      swapped =
        graphemes
        |> List.replace_at(i, Enum.at(graphemes, j))
        |> List.replace_at(j, Enum.at(graphemes, i))
        |> Enum.join()

      %{ed | buffer: swapped, cursor: min(len, new_cursor), redo: []}
    end
  end

  @doc "Swap the word under the cursor with the previous word."
  @spec transpose_words(t()) :: t()
  def transpose_words(%LE{} = ed) do
    graphemes = String.graphemes(ed.buffer)

    with {:ok, {w2_start, w2_end}} <- word_at(graphemes, ed.cursor),
         {:ok, {w1_start, w1_end}} <- word_before(graphemes, w2_start),
         true <- w1_end <= w2_start do
      before_ = Enum.slice(graphemes, 0, w1_start) |> Enum.join()
      w1 = Enum.slice(graphemes, w1_start, w1_end - w1_start) |> Enum.join()
      mid = Enum.slice(graphemes, w1_end, w2_start - w1_end) |> Enum.join()
      w2 = Enum.slice(graphemes, w2_start, w2_end - w2_start) |> Enum.join()
      tail = Enum.slice(graphemes, w2_end, length(graphemes)) |> Enum.join()
      ed = snapshot(ed)
      %{ed | buffer: before_ <> w2 <> mid <> w1 <> tail, cursor: w2_end, redo: []}
    else
      _ -> ed
    end
  end

  @doc "Apply `fun` to the word under/after the cursor."
  @spec change_word(t(), (String.t() -> String.t())) :: t()
  def change_word(%LE{} = ed, fun) when is_function(fun, 1) do
    graphemes = String.graphemes(ed.buffer)
    right = Enum.drop(graphemes, ed.cursor)

    case right do
      [] ->
        ed

      _ ->
        offset = next_word_offset(right)

        if offset == 0 do
          ed
        else
          ed = snapshot(ed)
          word = right |> Enum.take(offset) |> Enum.join()
          rest = right |> Enum.drop(offset) |> Enum.join()
          left = graphemes |> Enum.take(ed.cursor) |> Enum.join()
          new_buf = left <> fun.(word) <> rest
          %{ed | buffer: new_buf, cursor: ed.cursor + String.length(word), redo: []}
        end
    end
  end

  # -- Undo/redo -------------------------------------------------------------

  defp snapshot(%LE{} = ed) do
    entry = {ed.buffer, ed.cursor}
    undo = [entry | ed.undo] |> Enum.take(@undo_depth)
    %{ed | undo: undo}
  end

  @doc "Revert to the previous editor snapshot."
  @spec undo(t()) :: t()
  def undo(%LE{undo: []} = ed), do: ed

  def undo(%LE{undo: [{buf, cur} | rest]} = ed) do
    %{ed | buffer: buf, cursor: cur, undo: rest, redo: [{ed.buffer, ed.cursor} | ed.redo]}
  end

  @doc "Re-apply the most recently undone change."
  @spec redo(t()) :: t()
  def redo(%LE{redo: []} = ed), do: ed

  def redo(%LE{redo: [{buf, cur} | rest]} = ed) do
    %{ed | buffer: buf, cursor: cur, undo: [{ed.buffer, ed.cursor} | ed.undo], redo: rest}
  end

  # -- Word boundary helpers -------------------------------------------------

  @word_char ~r/[[:alnum:]_]/u

  defp word_char?(g), do: Regex.match?(@word_char, g)

  defp prev_word_index(graphemes) do
    # Walk right-to-left skipping non-word graphemes, then word graphemes.
    reversed = Enum.reverse(graphemes)

    {skipped_ws, rest} = Enum.split_while(reversed, &(not word_char?(&1)))
    {skipped_word, _} = Enum.split_while(rest, &word_char?/1)

    length(graphemes) - length(skipped_ws) - length(skipped_word)
  end

  defp next_word_offset(graphemes) do
    {skipped_ws, rest} = Enum.split_while(graphemes, &(not word_char?(&1)))
    {skipped_word, _} = Enum.split_while(rest, &word_char?/1)
    length(skipped_ws) + length(skipped_word)
  end

  defp word_at(graphemes, cursor) do
    # Find the boundaries of the word starting at or after `cursor`.
    right = Enum.drop(graphemes, cursor)
    skipped = Enum.take_while(right, &(not word_char?(&1))) |> length()
    word_start = cursor + skipped
    word_graphemes = Enum.drop(graphemes, word_start) |> Enum.take_while(&word_char?/1)

    case word_graphemes do
      [] -> :error
      _ -> {:ok, {word_start, word_start + length(word_graphemes)}}
    end
  end

  defp word_before(graphemes, cursor) do
    left = Enum.take(graphemes, cursor) |> Enum.reverse()
    skipped_ws = Enum.take_while(left, &(not word_char?(&1))) |> length()
    rest = Enum.drop(left, skipped_ws)
    word_len = Enum.take_while(rest, &word_char?/1) |> length()

    cond do
      word_len == 0 -> :error
      true -> {:ok, {cursor - skipped_ws - word_len, cursor - skipped_ws}}
    end
  end

  defp split(%LE{buffer: b, cursor: c}) do
    left = String.slice(b, 0, c)
    # Stepped-range `String.slice/2` is total: it returns a binary for
    # any in-bounds cursor, so the previous `|| ""` guard is dead code.
    right = String.slice(b, c..-1//1)
    {left, right}
  end

  defp push_kill(ring, ""), do: ring

  defp push_kill(ring, text) do
    ring = [text | ring]
    Enum.take(ring, @kill_ring_size)
  end

  defp capitalize(""), do: ""

  defp capitalize(word) do
    {first, rest} = String.split_at(word, 1)
    String.upcase(first) <> String.downcase(rest)
  end
end
