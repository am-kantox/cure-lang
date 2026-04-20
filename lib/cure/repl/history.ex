defmodule Cure.REPL.History do
  @moduledoc """
  Persistent, navigable history for the REPL.

  The history is stored as newline-separated entries in the file at
  `path/0`, trimmed to a rolling window of the most recent `@cap`
  entries. In-memory, entries are held oldest-first so we can cheaply
  append to the tail; the navigation cursor is a 0-based index counted
  from the newest entry (`0` meaning "empty buffer", `1` meaning "most
  recent entry"), which matches the usual Up/Down feel in `readline`.
  """

  alias __MODULE__, as: H

  @cap 10_000

  defstruct entries: [],
            path: nil,
            cursor: 0,
            draft: ""

  @type t :: %H{
          entries: [String.t()],
          path: String.t() | nil,
          cursor: non_neg_integer(),
          draft: String.t()
        }

  @doc """
  Load the history file at `path` (or start empty if missing).
  """
  @spec load(String.t() | nil) :: t()
  def load(nil), do: %H{}

  def load(path) do
    entries =
      case File.read(path) do
        {:ok, content} -> content |> String.split("\n", trim: true) |> Enum.take(-@cap)
        _ -> []
      end

    %H{entries: entries, path: path}
  end

  @doc "Append an entry (dedup consecutive duplicates). Persists to disk."
  @spec append(t(), String.t()) :: t()
  def append(%H{} = h, ""), do: h
  def append(%H{entries: [last | _]} = h, entry) when entry == last, do: h

  def append(%H{} = h, entry) do
    entries = Enum.take(h.entries ++ [entry], -@cap)
    new = %{h | entries: entries, cursor: 0, draft: ""}
    _ = persist(new)
    new
  end

  @doc "Persist the entire in-memory history to disk (atomic)."
  @spec persist(t()) :: :ok | {:error, term()}
  def persist(%H{path: nil}), do: :ok

  def persist(%H{path: path, entries: entries}) do
    tmp = path <> ".tmp"
    content = Enum.join(entries, "\n")

    with :ok <- File.write(tmp, content),
         :ok <- File.rename(tmp, path) do
      :ok
    end
  rescue
    e -> {:error, e}
  end

  @doc "Number of entries."
  @spec size(t()) :: non_neg_integer()
  def size(%H{entries: e}), do: length(e)

  @doc "Peek at the entries list (oldest first)."
  @spec entries(t()) :: [String.t()]
  def entries(%H{entries: e}), do: e

  @doc """
  Move one step toward older entries (the `Up` arrow).

  Returns `{:ok, entry, h}` with the entry text, or `:at_top` when the
  cursor has already reached the oldest entry.  The first call also
  saves the current `draft` so `down/1` can restore it.
  """
  @spec prev(t(), String.t()) :: {:ok, String.t(), t()} | :at_top
  def prev(%H{entries: []}, _draft), do: :at_top

  def prev(%H{cursor: c, entries: entries} = h, draft) do
    total = length(entries)

    if c >= total do
      :at_top
    else
      new_cursor = c + 1
      entry = Enum.at(entries, total - new_cursor)
      draft = if c == 0, do: draft, else: h.draft
      {:ok, entry, %{h | cursor: new_cursor, draft: draft}}
    end
  end

  @doc """
  Move one step toward newer entries (the `Down` arrow).

  Returns `{:ok, entry, h}` where `entry` may be the saved `draft` when
  the cursor walks past the newest entry, or `:at_bottom` when already
  at the draft.
  """
  @spec next(t()) :: {:ok, String.t(), t()} | :at_bottom
  def next(%H{cursor: 0}), do: :at_bottom

  def next(%H{cursor: 1} = h) do
    {:ok, h.draft, %{h | cursor: 0, draft: ""}}
  end

  def next(%H{cursor: c, entries: entries} = h) do
    new_cursor = c - 1
    entry = Enum.at(entries, length(entries) - new_cursor)
    {:ok, entry, %{h | cursor: new_cursor}}
  end

  @doc "Reset navigation cursor (after Enter submits a line)."
  @spec reset_cursor(t()) :: t()
  def reset_cursor(%H{} = h), do: %{h | cursor: 0, draft: ""}

  @doc """
  Incremental reverse search: find the most recent entry containing
  `needle` strictly older than `from` (a 1-based index from the newest).
  """
  @spec find_prev(t(), String.t(), non_neg_integer()) ::
          {:ok, String.t(), non_neg_integer()} | :not_found
  def find_prev(_h, "", _from), do: :not_found

  def find_prev(%H{entries: entries}, needle, from) do
    total = length(entries)
    start = max(from, 0)

    entries
    |> Enum.with_index(1)
    |> Enum.reverse()
    |> Enum.drop_while(fn {_e, idx} -> total - idx + 1 <= start end)
    |> Enum.find_value(:not_found, fn {e, idx} ->
      if e != "" and contains?(e, needle) do
        {:ok, e, total - idx + 1}
      end
    end)
  end

  @doc "Forward incremental search (Ctrl+S counterpart)."
  @spec find_next(t(), String.t(), non_neg_integer()) ::
          {:ok, String.t(), non_neg_integer()} | :not_found
  def find_next(_h, "", _from), do: :not_found

  def find_next(%H{entries: entries}, needle, from) do
    total = length(entries)

    entries
    |> Enum.with_index(1)
    |> Enum.find_value(:not_found, fn {e, idx} ->
      pos = total - idx + 1

      if pos < from and e != "" and contains?(e, needle) do
        {:ok, e, pos}
      end
    end)
  end

  @doc "Return the last `n` entries, newest-first."
  @spec tail(t(), non_neg_integer()) :: [String.t()]
  def tail(%H{entries: entries}, n) do
    entries |> Enum.reverse() |> Enum.take(n)
  end

  @doc "Substring search (case-insensitive) for the `:search` meta-command."
  @spec grep(t(), String.t()) :: [String.t()]
  def grep(%H{entries: entries}, needle) do
    Enum.filter(entries, &contains?(&1, needle))
  end

  defp contains?(haystack, needle) do
    String.contains?(String.downcase(haystack), String.downcase(needle))
  end
end
