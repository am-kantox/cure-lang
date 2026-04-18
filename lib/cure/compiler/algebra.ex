defmodule Cure.Compiler.Algebra do
  @moduledoc """
  Pretty-printing algebra modelled on Elixir's `Inspect.Algebra`, which
  in turn follows Wadler's "A prettier printer".

  The algebra represents documents as a tree of combinators:

    * `:doc_nil` -- the empty document.
    * `{:doc_cons, a, b}` -- concatenation.
    * `{:doc_string, binary, length}` -- a raw string with precomputed length.
    * `{:doc_nest, doc, indent}` -- increase the nesting indent of the
      nested document by `indent` columns.
    * `{:doc_break, string}` -- a soft break: renders as `string` in
      flat mode and as a newline (plus the current indent) in break mode.
    * `{:doc_line, count}` -- a hard newline (optionally stacked).
    * `{:doc_group, doc}` -- commit to flat mode if the group fits
      within the remaining width, otherwise commit to break mode.

  The output of `format/2` is an iolist; the caller decides whether to
  join it into a binary with `IO.iodata_to_binary/1`.
  """

  @type t ::
          :doc_nil
          | {:doc_cons, t(), t()}
          | {:doc_string, binary(), non_neg_integer()}
          | {:doc_nest, t(), non_neg_integer()}
          | {:doc_break, binary()}
          | {:doc_line, pos_integer()}
          | {:doc_group, t()}

  @typep mode :: :flat | :break

  # -- Constructors -----------------------------------------------------------

  @doc "The empty document."
  @spec empty() :: t()
  def empty, do: :doc_nil

  @doc "Wrap a literal string. Newlines inside the string are forbidden; use `line/0`."
  @spec string(binary()) :: t()
  def string(""), do: :doc_nil

  def string(str) when is_binary(str) do
    {:doc_string, str, :erlang.iolist_size(str)}
  end

  @doc "Concatenate two documents."
  @spec concat(t(), t()) :: t()
  def concat(:doc_nil, b), do: b
  def concat(a, :doc_nil), do: a
  def concat(a, b), do: {:doc_cons, a, b}

  @doc "Concatenate a list of documents."
  @spec concat([t()]) :: t()
  def concat(list) when is_list(list) do
    Enum.reduce(list, :doc_nil, fn doc, acc -> concat(acc, doc) end)
  end

  @doc "Increase the nesting indent of `doc` by `n`."
  @spec nest(t(), non_neg_integer()) :: t()
  def nest(:doc_nil, _n), do: :doc_nil
  def nest(doc, 0), do: doc
  def nest(doc, n) when is_integer(n) and n > 0, do: {:doc_nest, doc, n}

  @doc """
  Soft break: renders as the given string (default `\" \"`) in flat mode and
  as a newline in break mode.
  """
  @spec break() :: t()
  def break, do: {:doc_break, " "}

  @spec break(binary()) :: t()
  def break(str) when is_binary(str), do: {:doc_break, str}

  @doc "Hard newline (unconditional)."
  @spec line() :: t()
  def line, do: {:doc_line, 1}

  @doc "A stack of `n` newlines -- useful for blank lines between definitions."
  @spec line(pos_integer()) :: t()
  def line(n) when is_integer(n) and n >= 1, do: {:doc_line, n}

  @doc "A single literal space."
  @spec space() :: t()
  def space, do: string(" ")

  @doc "Concatenate `a` and `b` with a single space between them."
  @spec space(t(), t()) :: t()
  def space(a, b), do: concat([a, string(" "), b])

  @doc """
  Form a grouping boundary. When the group fits flat in the remaining
  width, every soft break inside renders flat. Otherwise every soft
  break renders as a newline at the current indent.
  """
  @spec group(t()) :: t()
  def group(:doc_nil), do: :doc_nil
  def group(doc), do: {:doc_group, doc}

  @doc "Join a list of documents with `separator` (default: `break()`)."
  @spec fold([t()], t()) :: t()
  def fold([], _sep), do: :doc_nil
  def fold([single], _sep), do: single
  def fold([head | rest], sep), do: concat([head, sep, fold(rest, sep)])

  # -- Rendering --------------------------------------------------------------

  @doc """
  Render `doc` to an iolist using the given width. Lines that would
  otherwise exceed `width` columns are broken at the closest enclosing
  `group/1`.
  """
  @spec format(t(), non_neg_integer()) :: iodata()
  def format(doc, width) when is_integer(width) and width >= 0 do
    render(width, 0, [{0, :flat, doc}])
  end

  # The core rendering loop. Each frame is `{indent, mode, doc}`:
  #
  #   * `indent` -- the current indent column for any emitted newline.
  #   * `mode`   -- `:flat` (inline everything) or `:break` (every soft
  #                  break is a newline).
  #   * `doc`    -- the unprocessed subdocument.
  #
  # `width` is the target line width; `col` is the current column.

  @spec render(non_neg_integer(), non_neg_integer(), [{non_neg_integer(), mode(), t()}]) :: iodata()
  defp render(_width, _col, []), do: []

  defp render(width, col, [{_indent, _mode, :doc_nil} | rest]) do
    render(width, col, rest)
  end

  defp render(width, col, [{indent, mode, {:doc_cons, a, b}} | rest]) do
    render(width, col, [{indent, mode, a}, {indent, mode, b} | rest])
  end

  defp render(width, col, [{indent, mode, {:doc_nest, inner, n}} | rest]) do
    render(width, col, [{indent + n, mode, inner} | rest])
  end

  defp render(width, col, [{_indent, _mode, {:doc_string, str, len}} | rest]) do
    [str | render(width, col + len, rest)]
  end

  defp render(width, _col, [{indent, _mode, {:doc_line, n}} | rest]) do
    [String.duplicate("\n", n), String.duplicate(" ", indent) | render(width, indent, rest)]
  end

  defp render(width, col, [{_indent, :flat, {:doc_break, str}} | rest]) do
    [str | render(width, col + byte_size(str), rest)]
  end

  defp render(width, _col, [{indent, :break, {:doc_break, _str}} | rest]) do
    [?\n, String.duplicate(" ", indent) | render(width, indent, rest)]
  end

  defp render(width, col, [{indent, _mode, {:doc_group, inner}} | rest]) do
    mode = if fits?(width - col, [{indent, :flat, inner}]), do: :flat, else: :break
    render(width, col, [{indent, mode, inner} | rest])
  end

  # `fits?(remaining, frames)` asks whether the upcoming flat rendering
  # of `frames` stays within `remaining` columns. Any break or newline
  # short-circuits with `true` because it implies the rest of the line
  # is untouched by the group currently being measured.

  @spec fits?(integer(), [{non_neg_integer(), mode(), t()}]) :: boolean()
  defp fits?(remaining, _frames) when remaining < 0, do: false
  defp fits?(_remaining, []), do: true
  defp fits?(remaining, [{_i, _m, :doc_nil} | rest]), do: fits?(remaining, rest)

  defp fits?(remaining, [{i, m, {:doc_cons, a, b}} | rest]) do
    fits?(remaining, [{i, m, a}, {i, m, b} | rest])
  end

  defp fits?(remaining, [{i, m, {:doc_nest, inner, n}} | rest]) do
    fits?(remaining, [{i + n, m, inner} | rest])
  end

  defp fits?(remaining, [{_i, _m, {:doc_string, _str, len}} | rest]) do
    fits?(remaining - len, rest)
  end

  defp fits?(_remaining, [{_i, _m, {:doc_line, _n}} | _rest]), do: true

  defp fits?(remaining, [{_i, :flat, {:doc_break, str}} | rest]) do
    fits?(remaining - byte_size(str), rest)
  end

  defp fits?(_remaining, [{_i, :break, {:doc_break, _str}} | _rest]), do: true

  defp fits?(remaining, [{i, m, {:doc_group, inner}} | rest]) do
    fits?(remaining, [{i, m, inner} | rest])
  end
end
