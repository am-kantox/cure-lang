defmodule Cure.REPL.Search do
  @moduledoc """
  Incremental reverse-i-search (bound to `Ctrl+R`) and its forward
  counterpart (`Ctrl+S`).

  The search loop is a *mini* editor: the user's keystrokes accumulate
  into a `needle` that is matched against the history (via
  `Cure.REPL.History.find_prev/3`), and the best current match is echoed
  back. When the user hits:

  * `Enter` -- the matched line becomes the main editor's buffer and the
    outer REPL continues as if that line had been submitted.
  * `Esc` / `Ctrl+G` -- the search is aborted, the original buffer
    restored.
  * `Ctrl+R` -- step to the next older hit.
  * `Ctrl+S` -- reverse direction (forward).
  * Any cursor-movement or editing key -- accept the match into the
    main editor and immediately dispatch the key so the outer editor
    keeps the flow going ("accept-and-edit").
  """

  alias Cure.REPL.{History, Theme}

  defstruct needle: "",
            direction: :reverse,
            match: nil,
            position: 0,
            original: ""

  @type direction :: :reverse | :forward
  @type t :: %__MODULE__{
          needle: String.t(),
          direction: direction(),
          match: String.t() | nil,
          position: non_neg_integer(),
          original: String.t()
        }

  @doc "Create a fresh search state, remembering the pre-search buffer."
  @spec new(String.t()) :: t()
  def new(original), do: %__MODULE__{original: original}

  @doc """
  Handle a key inside the search loop.

  Returns one of:

    * `{:continue, t()}` -- keep searching, just redraw.
    * `{:accept, String.t()}` -- user pressed Enter on a match; caller
       should put this text into the editor and submit as usual.
    * `{:accept_and_key, String.t(), key}` -- accept the match as the
       new editor buffer *and* immediately feed `key` back to the
       editor (arrow keys, Ctrl+A, ...).
    * `{:cancel, String.t()}` -- abort, restore `original`.
  """
  @spec handle(t(), Cure.REPL.Terminal.key(), History.t()) ::
          {:continue, t()}
          | {:accept, String.t()}
          | {:accept_and_key, String.t(), Cure.REPL.Terminal.key()}
          | {:cancel, String.t()}
  def handle(s, key, history) do
    case key do
      :enter ->
        {:accept, match_or_original(s)}

      :esc ->
        {:cancel, s.original}

      {:ctrl, ?G} ->
        {:cancel, s.original}

      {:ctrl, ?C} ->
        {:cancel, s.original}

      {:ctrl, ?R} ->
        {:continue, step(s, :reverse, history)}

      {:ctrl, ?S} ->
        {:continue, step(s, :forward, history)}

      :backspace ->
        {:continue, shrink(s, history)}

      {:ctrl, ?H} ->
        {:continue, shrink(s, history)}

      {:key, ch} ->
        {:continue, grow(s, ch, history)}

      _editing when key in [:left, :right, :up, :down, :home, :end] ->
        {:accept_and_key, match_or_original(s), key}

      _ ->
        {:continue, s}
    end
  end

  @doc "Format the status line for `Cure.REPL.Render.draw_search_status/2`."
  @spec status(t(), Theme.t()) :: String.t()
  def status(s, %Theme{} = theme) do
    direction =
      case s.direction do
        :reverse -> "(reverse-i-search)"
        :forward -> "(i-search)"
      end

    match = s.match || theme.dim <> "(no match)" <> theme.reset
    theme.info <> direction <> theme.reset <> " '" <> theme.search <> s.needle <> theme.reset <> "': " <> match
  end

  defp match_or_original(%__MODULE__{match: nil, original: o}), do: o
  defp match_or_original(%__MODULE__{match: m}), do: m

  defp grow(s, ch, history) do
    needle = s.needle <> ch
    search_from_start(%{s | needle: needle}, history)
  end

  defp shrink(%__MODULE__{needle: ""} = s, _history), do: s

  defp shrink(%__MODULE__{needle: needle} = s, history) do
    shorter = String.slice(needle, 0, String.length(needle) - 1)
    search_from_start(%{s | needle: shorter}, history)
  end

  defp step(s, direction, history) do
    s = %{s | direction: direction}
    total = length(History.entries(history))

    result =
      case direction do
        :reverse -> History.find_prev(history, s.needle, s.position)
        :forward -> History.find_next(history, s.needle, s.position)
      end

    case result do
      {:ok, match, pos} -> %{s | match: match, position: pos}
      :not_found -> %{s | match: nil, position: if(direction == :reverse, do: total, else: 0)}
    end
  end

  defp search_from_start(s, history) do
    total = length(History.entries(history))

    case History.find_prev(history, s.needle, 0) do
      {:ok, match, pos} -> %{s | match: match, position: pos, direction: :reverse}
      :not_found -> %{s | match: nil, position: total}
    end
  end
end
