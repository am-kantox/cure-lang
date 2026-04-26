defmodule Cure.Story do
  @moduledoc """
  Narrative architecture document generator for Cure projects (v0.32.0).

  Reads every `.cure` source file under the project root, builds a
  structural outline (apps -> supervisors -> actors -> FSMs -> types),
  and emits a readable `STORY.md` that introduces the system top-down.

  ## Usage

      # Generate STORY.md in the current project
      {:ok, path} = Cure.Story.generate(".")

      # Generate to a custom path
      {:ok, path} = Cure.Story.generate(".", out: "docs/ARCHITECTURE.md")

      # Print to stdout without writing a file
      {:ok, content} = Cure.Story.generate(".", stdout: true)

  See `Mix.Tasks.Cure.Story` for the CLI interface (`cure story`).
  """

  alias Cure.Story.{Narrator, Outline}

  @doc """
  Generate a narrative document from the project at `root`.

  ## Options

    * `:out` -- output file path. Defaults to `STORY.md` at the project root.
    * `:stdout` -- when `true`, return the content as `{:ok, content}` without
      writing a file.
    * `:diagrams` -- when `true`, embed Mermaid state-diagram code blocks for
      each FSM. Requires a Mermaid-aware renderer. Default: `false`.
    * `:format` -- `:md` (default) or `:html` (wraps the Markdown in a minimal
      HTML shell via `Cure.Doc.HtmlGenerator`).
    * `:project_name` -- project name used as the document title. When not
      provided, the `[project].name` value from `Cure.toml` is used.

  Returns `{:ok, path}` when a file was written, `{:ok, content}` when
  `stdout: true` is set, or `{:error, reason}` on failure.
  """
  @spec generate(String.t(), keyword()) :: {:ok, String.t()} | {:error, term()}
  def generate(root \\ ".", opts \\ []) do
    out_path = Keyword.get(opts, :out, Path.join(root, "STORY.md"))
    stdout? = Keyword.get(opts, :stdout, false)
    diagrams? = Keyword.get(opts, :diagrams, false)
    format = Keyword.get(opts, :format, :md)
    project_name = Keyword.get(opts, :project_name, read_project_name(root))

    outline = Outline.build(root)
    md = Narrator.narrate(outline, diagrams: diagrams?, project_name: project_name)

    content =
      case format do
        :html -> wrap_html(md, project_name)
        _ -> md
      end

    if stdout? do
      {:ok, content}
    else
      case File.write(out_path, content) do
        :ok -> {:ok, out_path}
        {:error, reason} -> {:error, {:file_write_error, out_path, reason}}
      end
    end
  end

  # -- Helpers ------------------------------------------------------------------

  defp read_project_name(root) do
    case Cure.Project.load(root) do
      {:ok, %{name: name}} when is_binary(name) and name != "" -> name
      _ -> "Project"
    end
  end

  defp wrap_html(md, title) do
    # Minimal HTML shell around the Markdown content.
    # A real implementation would use Cure.Doc.HtmlGenerator.
    escaped_title = html_escape(title)

    """
    <!DOCTYPE html>
    <html lang="en">
    <head>
      <meta charset="UTF-8">
      <title>#{escaped_title} -- Story</title>
      <style>
        body { font-family: sans-serif; max-width: 860px; margin: 2rem auto; padding: 0 1rem; }
        code { background: #f4f4f4; padding: 2px 4px; border-radius: 3px; }
        pre code { background: none; padding: 0; }
      </style>
    </head>
    <body>
    <pre>#{html_escape(md)}</pre>
    </body>
    </html>
    """
  end

  defp html_escape(str) when is_binary(str) do
    str
    |> String.replace("&", "&amp;")
    |> String.replace("<", "&lt;")
    |> String.replace(">", "&gt;")
    |> String.replace("\"", "&quot;")
  end
end
