defmodule Cure.Doc.HTMLGenerator do
  @moduledoc """
  Generates static HTML documentation from extracted doc maps.

  Produces one HTML file per module plus an index page.
  Uses embedded templates (no EEx dependency required).
  """

  @doc """
  Generate HTML documentation for a list of module doc maps.

  Writes HTML files to the given output directory.
  Returns `:ok` on success.
  """
  @spec generate([map()], String.t(), keyword()) :: :ok
  def generate(modules, output_dir, opts \\ []) do
    title = Keyword.get(opts, :title, "Cure Documentation")
    File.mkdir_p!(output_dir)

    # Write CSS
    File.write!(Path.join(output_dir, "style.css"), css())

    # Write index
    index_html = render_index(modules, title)
    File.write!(Path.join(output_dir, "index.html"), index_html)

    # Write per-module pages
    Enum.each(modules, fn mod ->
      filename = module_filename(mod.module)
      html = render_module(mod, title)
      File.write!(Path.join(output_dir, filename), html)
    end)

    :ok
  end

  # -- Index Page ---------------------------------------------------------------

  defp render_index(modules, title) do
    module_links =
      modules
      |> Enum.sort_by(& &1.module)
      |> Enum.map(fn mod ->
        filename = module_filename(mod.module)
        doc_preview = if mod.module_doc, do: truncate(mod.module_doc, 80), else: ""
        fn_count = length(mod.functions)

        """
        <li>
          <a href="#{filename}"><span class="mod-name">#{esc(mod.module)}</span></a>
          <span class="mod-count">#{fn_count} functions</span>
          <span class="mod-doc">#{esc(doc_preview)}</span>
        </li>
        """
      end)
      |> Enum.join("\n")

    wrap_page(title, """
    <h1>#{esc(title)}</h1>
    <p>#{length(modules)} modules</p>
    <ul class="module-list">
    #{module_links}
    </ul>
    """)
  end

  # -- Module Page --------------------------------------------------------------

  defp render_module(mod, title) do
    module_doc_html =
      if mod.module_doc do
        "<div class=\"module-doc\">#{markdown_to_html(mod.module_doc)}</div>"
      else
        ""
      end

    types_html = render_types(mod.types)
    protocols_html = render_protocols(mod.protocols)
    functions_html = render_functions(mod.functions)

    wrap_page("#{mod.module} - #{title}", """
    <nav><a href="index.html">Index</a></nav>
    <h1>#{esc(mod.module)}</h1>
    #{module_doc_html}
    #{types_html}
    #{protocols_html}
    <h2>Functions</h2>
    #{functions_html}
    """)
  end

  defp render_functions(functions) do
    public_fns = Enum.filter(functions, &(&1.visibility == :public))

    if public_fns == [] do
      "<p>No public functions.</p>"
    else
      Enum.map_join(public_fns, "\n", &render_function/1)
    end
  end

  defp render_function(f) do
    params_str =
      Enum.map_join(f.params, ", ", fn {name, type} ->
        "#{esc(name)}: <span class=\"type\">#{esc(type)}</span>"
      end)

    ret_str = if f.return_type, do: " -> <span class=\"type\">#{esc(f.return_type)}</span>", else: ""

    effects_str =
      if f.effects != [] do
        effs = Enum.join(f.effects, ", ")
        " <span class=\"effect\">! #{esc(effs)}</span>"
      else
        ""
      end

    badges =
      [
        if(f.extern, do: "<span class=\"badge extern\">extern</span>", else: nil),
        if(f.guards, do: "<span class=\"badge guard\">guarded</span>", else: nil),
        if(f.clauses > 1, do: "<span class=\"badge clauses\">#{f.clauses} clauses</span>", else: nil)
      ]
      |> Enum.reject(&is_nil/1)
      |> Enum.join(" ")

    doc_html =
      if f.doc do
        "<div class=\"fn-doc\">#{markdown_to_html(f.doc)}</div>"
      else
        ""
      end

    """
    <div class="function" id="fn-#{esc(f.name)}">
      <h3>
        <span class="kw">fn</span> <span class="fn-name">#{esc(f.name)}</span>(#{params_str})#{ret_str}#{effects_str}
        #{badges}
      </h3>
      #{doc_html}
    </div>
    """
  end

  defp render_types([]), do: ""

  defp render_types(types) do
    items =
      Enum.map_join(types, "\n", fn t ->
        doc = if t.doc, do: "<p>#{esc(t.doc)}</p>", else: ""

        variants =
          if Map.has_key?(t, :variants) do
            " = " <> Enum.join(t.variants, " | ")
          else
            if t.refinement, do: " (refinement)", else: ""
          end

        "<li><code>type #{esc(t.name)}#{esc(variants)}</code>#{doc}</li>"
      end)

    "<h2>Types</h2><ul class=\"type-list\">#{items}</ul>"
  end

  defp render_protocols([]), do: ""

  defp render_protocols(protocols) do
    items =
      Enum.map_join(protocols, "\n", fn p ->
        tp = if p.type_params != [], do: "(#{Enum.join(p.type_params, ", ")})", else: ""
        methods = Enum.map_join(p.methods, ", ", & &1.name)
        doc = if p.doc, do: "<p>#{esc(p.doc)}</p>", else: ""
        "<li><code>proto #{esc(p.name)}#{esc(tp)}</code> -- #{esc(methods)}#{doc}</li>"
      end)

    "<h2>Protocols</h2><ul class=\"proto-list\">#{items}</ul>"
  end

  # -- HTML Helpers -------------------------------------------------------------

  defp wrap_page(title, body) do
    """
    <!DOCTYPE html>
    <html lang="en">
    <head>
      <meta charset="utf-8">
      <meta name="viewport" content="width=device-width, initial-scale=1">
      <title>#{esc(title)}</title>
      <link rel="stylesheet" href="style.css">
    </head>
    <body>
      <main>
      #{body}
      </main>
      <footer>Generated by <code>cure doc</code></footer>
    </body>
    </html>
    """
  end

  defp module_filename(name) do
    name
    |> String.replace(".", "_")
    |> String.downcase()
    |> Kernel.<>(".html")
  end

  defp esc(nil), do: ""

  defp esc(s) when is_binary(s) do
    s
    |> String.replace("&", "&amp;")
    |> String.replace("<", "&lt;")
    |> String.replace(">", "&gt;")
    |> String.replace("\"", "&quot;")
  end

  defp esc(other), do: esc(to_string(other))

  defp truncate(s, max) do
    if String.length(s) > max do
      String.slice(s, 0, max) <> "..."
    else
      s
    end
  end

  defp markdown_to_html(text) do
    text
    |> String.split("\n")
    |> Enum.map(fn line ->
      line = esc(line)

      cond do
        String.starts_with?(line, "  ") -> "<code>#{line}</code>"
        line == "" -> "<br>"
        true -> line
      end
    end)
    |> Enum.join("\n")
    |> then(&"<p>#{&1}</p>")
  end

  # -- CSS ----------------------------------------------------------------------

  defp css do
    """
    :root {
      --bg: #fafafa;
      --fg: #1a1a2e;
      --accent: #2563eb;
      --border: #e5e7eb;
      --code-bg: #f3f4f6;
      --fn-bg: #fff;
    }

    @media (prefers-color-scheme: dark) {
      :root {
        --bg: #0f172a;
        --fg: #e2e8f0;
        --accent: #60a5fa;
        --border: #334155;
        --code-bg: #1e293b;
        --fn-bg: #1e293b;
      }
    }

    * { margin: 0; padding: 0; box-sizing: border-box; }

    body {
      font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
      background: var(--bg);
      color: var(--fg);
      line-height: 1.6;
      max-width: 900px;
      margin: 0 auto;
      padding: 2rem 1rem;
    }

    h1 { margin-bottom: 0.5rem; }
    h2 { margin: 2rem 0 1rem; border-bottom: 1px solid var(--border); padding-bottom: 0.3rem; }
    h3 { font-size: 1rem; font-weight: 600; }

    nav { margin-bottom: 1.5rem; }
    nav a { color: var(--accent); text-decoration: none; }
    nav a:hover { text-decoration: underline; }

    .module-list { list-style: none; }
    .module-list li { padding: 0.5rem 0; border-bottom: 1px solid var(--border); }
    .mod-name { font-weight: 600; color: var(--accent); }
    .mod-count { margin-left: 1rem; font-size: 0.85rem; opacity: 0.6; }
    .mod-doc { display: block; font-size: 0.85rem; opacity: 0.7; margin-top: 0.2rem; }

    .function {
      background: var(--fn-bg);
      border: 1px solid var(--border);
      border-radius: 6px;
      padding: 1rem;
      margin-bottom: 1rem;
    }

    .kw { color: #9333ea; font-weight: 600; }
    .fn-name { color: var(--accent); }
    .type { color: #059669; }
    .effect { color: #dc2626; font-weight: 500; }

    .badge {
      font-size: 0.7rem;
      padding: 0.15rem 0.4rem;
      border-radius: 3px;
      vertical-align: middle;
      margin-left: 0.3rem;
    }
    .badge.extern { background: #fef3c7; color: #92400e; }
    .badge.guard { background: #dbeafe; color: #1e40af; }
    .badge.clauses { background: #f3e8ff; color: #6b21a8; }

    .fn-doc, .module-doc { margin-top: 0.5rem; font-size: 0.9rem; line-height: 1.5; }
    .fn-doc code, .module-doc code {
      background: var(--code-bg);
      padding: 0.1rem 0.3rem;
      border-radius: 3px;
      font-size: 0.85em;
    }

    .type-list, .proto-list { list-style: none; margin-left: 0; }
    .type-list li, .proto-list li { padding: 0.3rem 0; }
    .type-list code, .proto-list code {
      background: var(--code-bg);
      padding: 0.2rem 0.5rem;
      border-radius: 3px;
    }

    footer {
      margin-top: 3rem;
      padding-top: 1rem;
      border-top: 1px solid var(--border);
      font-size: 0.8rem;
      opacity: 0.5;
    }
    """
  end
end
