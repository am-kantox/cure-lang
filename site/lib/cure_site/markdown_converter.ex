defmodule CureSite.MarkdownConverter do
  @moduledoc """
  Custom HTML converter for NimblePublisher.

  Uses Earmark for Markdown rendering and NimblePublisher's
  built-in highlighting with the configured highlighters.
  """

  def convert(filepath, body, _attrs, opts) do
    if Path.extname(filepath) in [".md", ".markdown"] do
      highlighters = Keyword.get(opts, :highlighters, [])

      body
      |> Earmark.as_html!()
      |> NimblePublisher.highlight(highlighters)
    end
  end
end
