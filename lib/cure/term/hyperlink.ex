defmodule Cure.Term.Hyperlink do
  @moduledoc """
  OSC 8 terminal hyperlinks for Cure diagnostics (v0.27.0).

  Many modern terminals support the OSC 8 hyperlink escape sequence, which
  turns arbitrary text into a clickable link pointing at any URI, including
  `file://` URIs with optional line/column fragments. This module is the
  single entry point used by the REPL, LSP, CLI, and compiler-error paths
  so that all three wrap filepaths and file+line coordinates identically.

  ## Emission

  `emit/1` decides whether hyperlinks are supported in the current
  environment and returns a boolean. Emission is enabled when:

  - `IO.ANSI.enabled?/0` returns `true` (stdout is a tty and colours are
    not explicitly disabled), AND
  - the `NO_COLOR` environment variable is not set to a non-empty value,
    AND
  - the current `TERM` variable matches one of the known-good terminal
    families (`wezterm`, `xterm-kitty`, `iterm`, `iterm2`, `vte`,
    `warp`), OR the `CURE_HYPERLINKS` environment variable is set to
    a truthy value (`1`, `yes`, `true`, `on`, case-insensitive).

  Callers may force emission off with `CURE_HYPERLINKS=0` regardless of
  terminal detection, which is the escape hatch used by tests and CI
  runners that capture stdout.

  ## Rendering

  Two convenience wrappers are provided:

  - `file_link/2` produces a hyperlink to a file (`file://<abs>`), using
    the relative path as the visible label.
  - `file_line_link/3` adds an `#L<line>` fragment to the URI so that
    terminals that understand line anchors (WezTerm, VTE, Kitty,
    iTerm2, Warp) jump directly to the offending line.

  If emission is disabled, both helpers return the plain label unchanged.

  ## Raw API

  `wrap/2` is the low-level helper that emits a raw OSC 8 sequence. It
  is used by all the higher-level helpers and is also exposed so that
  non-file links (for instance, `https://...` in REPL banners) can reuse
  the same emission gate.
  """

  @known_terms ~w(wezterm xterm-kitty iterm iterm2 vte warp)

  @doc """
  True when the current stdout supports OSC 8 hyperlinks.
  """
  @spec emit?() :: boolean()
  def emit? do
    cond do
      no_color?() -> false
      forced_off?() -> false
      forced_on?() -> true
      not ansi_enabled?() -> false
      true -> known_term?(System.get_env("TERM"))
    end
  end

  @doc """
  Wrap `label` in an OSC 8 hyperlink pointing at `uri`.

  If the terminal does not support hyperlinks, `label` is returned
  unchanged.
  """
  @spec wrap(String.t(), String.t()) :: String.t()
  def wrap(uri, label) when is_binary(uri) and is_binary(label) do
    if emit?() do
      # OSC 8 ; params ; URI ST <text> OSC 8 ; ; ST
      "\e]8;;#{uri}\e\\#{label}\e]8;;\e\\"
    else
      label
    end
  end

  @doc """
  Produce an OSC 8 hyperlink to `path`. Relative paths are expanded to
  absolute paths so the `file://` URI is valid regardless of the
  terminal's current working directory. The label is the original
  (possibly relative) path for readability.
  """
  @spec file_link(String.t(), Keyword.t()) :: String.t()
  def file_link(path, opts \\ []) when is_binary(path) do
    label = Keyword.get(opts, :label, path)

    case absolute_uri(path) do
      {:ok, uri} -> wrap(uri, label)
      :error -> label
    end
  end

  @doc """
  Like `file_link/2` but appends a `#L<line>` (and optional `C<col>`)
  fragment so terminals that understand line anchors jump straight to
  the line.
  """
  @spec file_line_link(String.t(), non_neg_integer(), Keyword.t()) :: String.t()
  def file_line_link(path, line, opts \\ []) when is_binary(path) and is_integer(line) do
    col = Keyword.get(opts, :col, 0)

    label =
      Keyword.get_lazy(opts, :label, fn ->
        if line > 0, do: "#{path}:#{line}", else: path
      end)

    case absolute_uri(path) do
      {:ok, uri} ->
        anchored =
          cond do
            line > 0 and col > 0 -> uri <> "#L#{line}C#{col}"
            line > 0 -> uri <> "#L#{line}"
            true -> uri
          end

        wrap(anchored, label)

      :error ->
        label
    end
  end

  # -- Internals --------------------------------------------------------------

  defp absolute_uri(path) do
    abs =
      cond do
        path in ["", "nofile"] -> nil
        Path.type(path) == :absolute -> path
        true -> Path.expand(path)
      end

    case abs do
      nil -> :error
      p -> {:ok, "file://" <> uri_encode(p)}
    end
  end

  # Conservative URI escaping -- keep ASCII alnum, `/`, `.`, `_`, `-`, `~`
  # literal, percent-encode everything else. Sufficient for filesystem
  # paths on Linux/macOS/WSL.
  defp uri_encode(bin) do
    bin
    |> :erlang.binary_to_list()
    |> Enum.map_join(&encode_byte/1)
  end

  defp encode_byte(byte) when byte in ?a..?z, do: <<byte>>
  defp encode_byte(byte) when byte in ?A..?Z, do: <<byte>>
  defp encode_byte(byte) when byte in ?0..?9, do: <<byte>>
  defp encode_byte(byte) when byte in [?/, ?., ?_, ?-, ?~], do: <<byte>>
  defp encode_byte(byte), do: ("%" <> Integer.to_string(byte, 16)) |> pad_hex()

  defp pad_hex("%" <> rest) when byte_size(rest) == 1, do: "%0" <> rest
  defp pad_hex(other), do: other

  defp no_color? do
    case System.get_env("NO_COLOR") do
      nil -> false
      "" -> false
      _ -> true
    end
  end

  defp forced_off? do
    case System.get_env("CURE_HYPERLINKS") do
      v when v in ["0", "no", "false", "off"] -> true
      _ -> false
    end
  end

  defp forced_on? do
    case System.get_env("CURE_HYPERLINKS") do
      v when is_binary(v) and v not in ["", "0", "no", "false", "off"] -> true
      _ -> false
    end
  end

  defp ansi_enabled? do
    # IO.ANSI.enabled?/0 is false under typical test / pipe conditions,
    # which is exactly what we want: we never emit hyperlinks into a
    # file or a captured test output.
    apply(IO.ANSI, :enabled?, [])
  end

  defp known_term?(nil), do: false

  defp known_term?(term) when is_binary(term) do
    lower = String.downcase(term)
    Enum.any?(@known_terms, &String.contains?(lower, &1))
  end
end
