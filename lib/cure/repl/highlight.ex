defmodule Cure.REPL.Highlight do
  @moduledoc """
  ANSI syntax highlighting for Cure source text.

  Produces ANSI-decorated strings using `Makeup.Lexers.CureLexer` for
  tokenisation and `Marcli.Formatter` for the token-to-ANSI mapping
  (which in turn uses the `Marcli.Theme` palette). A small in-memory
  cache keyed by `:erlang.phash2/1` avoids re-lexing the buffer on every
  keystroke redraw.

  Graceful degradation: if the lexer crashes mid-token (very common
  while the user is still typing) we return the original text
  unchanged.
  """

  @ets :cure_repl_highlight_cache
  @cache_size 128

  @doc "Lazily initialize the ETS cache."
  @spec ensure_cache() :: :ok
  def ensure_cache do
    case :ets.whereis(@ets) do
      :undefined ->
        _ = :ets.new(@ets, [:named_table, :public, :set, read_concurrency: true])
        :ok

      _ ->
        :ok
    end
  rescue
    ArgumentError -> :ok
  end

  @doc "Return an ANSI-highlighted version of `source`, or the original on failure."
  @spec highlight(String.t(), keyword()) :: String.t()
  def highlight(source, opts \\ []) when is_binary(source) do
    if enabled?() do
      do_highlight(source, opts)
    else
      source
    end
  end

  defp enabled? do
    Code.ensure_loaded?(Makeup.Lexers.CureLexer) and
      Code.ensure_loaded?(Marcli.Formatter) and
      Code.ensure_loaded?(Marcli.Theme)
  end

  defp do_highlight(source, opts) do
    ensure_cache()
    key = {:erlang.phash2(source), Keyword.get(opts, :theme_name, :dark)}

    case :ets.lookup(@ets, key) do
      [{^key, cached}] ->
        cached

      [] ->
        result = lex_and_format(source, opts)
        maybe_insert(key, result)
        result
    end
  rescue
    _ -> source
  catch
    _, _ -> source
  end

  defp lex_and_format(source, opts) do
    try do
      tokens = Makeup.Lexers.CureLexer.lex(source, group_prefix: "repl")
      theme = Marcli.Theme.default()

      Marcli.Formatter.format_as_binary(tokens,
        syntax: Keyword.get(opts, :syntax, theme.syntax),
        reset: theme.reset
      )
    rescue
      _ -> source
    catch
      _, _ -> source
    end
  end

  defp maybe_insert(key, value) do
    size = :ets.info(@ets, :size)

    if is_integer(size) and size >= @cache_size do
      :ets.delete_all_objects(@ets)
    end

    :ets.insert(@ets, {key, value})
  rescue
    _ -> :ok
  end
end
