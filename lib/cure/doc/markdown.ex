defmodule Cure.Doc.Markdown do
  @moduledoc """
  Pure-Elixir Markdown-to-HTML renderer used by `cure doc`.

  Thin wrapper over the `Md` library with two extras on top of the
  upstream behaviour:

    * Placeholder interpolation: `{{cure_version}}` and `{{cure_vversion}}`
      are substituted before parsing so stdlib doc comments can carry
      release-sensitive copy without a preprocess step at the call
      site.
    * Syntax-highlighted fenced code blocks: when a code fence carries
      a known language (`cure`, `elixir`, `erlang`) the contents are
      run through `Makeup` so the generated HTML lines up visually
      with the rest of the Cure site. Unknown languages fall through
      to a plain `<pre><code class="language-...">` block.

  `Md` is NIF-free, so this module is safe to call from inside the
  escript -- unlike `marcli` + `MDEx`, whose Rust NIF cannot be loaded
  when the VM is bootstrapped out of an escript archive (see
  `Cure.REPL.Markdown`).
  """

  @doc """
  Render `markdown` (a binary) to an HTML fragment.

  Returns an empty string for nil / empty inputs so callers can blindly
  splice the result into a template.
  """
  @spec to_html(String.t() | nil) :: String.t()
  def to_html(nil), do: ""
  def to_html(""), do: ""

  def to_html(markdown) when is_binary(markdown) do
    markdown
    |> interpolate_placeholders()
    |> Md.generate()
    |> highlight_code_blocks()
  end

  @doc """
  Substitute compile-time placeholders inside `body`.

  Supported placeholders:

    * `{{cure_version}}`  -> bare Cure version (`\"0.28.2\"`).
    * `{{cure_vversion}}` -> prefixed Cure version (`\"v0.28.2\"`).
  """
  @spec interpolate_placeholders(String.t()) :: String.t()
  def interpolate_placeholders(body) when is_binary(body) do
    version = Cure.version()

    body
    |> String.replace("{{cure_version}}", version)
    |> String.replace("{{cure_vversion}}", "v" <> version)
  end

  # -- Syntax highlighting ----------------------------------------------------

  # `Md` emits code fences as `<pre><code class="<lang> lang-<lang>">...</code></pre>`.
  # For `cure`, `elixir`, and `erlang` we replace the inner text with
  # Makeup's tokenised output so the same highlighter powers both
  # `cure doc` and the Phoenix site.
  defp highlight_code_blocks(html) when is_binary(html) do
    Regex.replace(
      ~r|<pre><code class="(?<lang>[a-z0-9_-]+) lang-[a-z0-9_-]+">(?<body>.*?)</code></pre>|s,
      html,
      fn _match, lang, body ->
        highlight_block(lang, body)
      end
    )
  end

  defp highlight_block(lang, escaped_body) do
    body = unescape_html(escaped_body)

    case Map.get(lexers(), lang) do
      nil ->
        # Unknown language -> keep the raw block but emit a stable
        # class name that downstream CSS can target.
        """
        <pre class="cure-doc-code"><code class="language-#{lang}">#{escape_html(body)}</code></pre>
        """

      lexer ->
        highlighted =
          try do
            Makeup.highlight_inner_html(body, lexer: lexer)
          rescue
            _ -> escape_html(body)
          end

        """
        <pre class="cure-doc-code highlight"><code class="language-#{lang}">#{highlighted}</code></pre>
        """
    end
  end

  defp lexers do
    %{
      "cure" => Makeup.Lexers.CureLexer,
      "elixir" => Makeup.Lexers.ElixirLexer,
      "erlang" => Makeup.Lexers.ErlangLexer
    }
  end

  defp escape_html(s) do
    s
    |> String.replace("&", "&amp;")
    |> String.replace("<", "&lt;")
    |> String.replace(">", "&gt;")
  end

  defp unescape_html(s) do
    s
    |> String.replace("&lt;", "<")
    |> String.replace("&gt;", ">")
    |> String.replace("&quot;", "\"")
    |> String.replace("&#39;", "'")
    |> String.replace("&amp;", "&")
  end
end
