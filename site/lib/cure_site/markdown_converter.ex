defmodule CureSite.MarkdownConverter do
  @moduledoc """
  Custom HTML converter for NimblePublisher.

  Uses Earmark for Markdown rendering and NimblePublisher's
  built-in highlighting with the configured highlighters.

  Before rendering, a small set of placeholders is substituted so
  markdown content can reference build-time values such as the
  current Cure version:

    * `{{cure_version}}`  -> the bare version string (e.g. `0.17.0`)
    * `{{cure_vversion}}` -> the version prefixed with `v`
      (e.g. `v0.17.0`)
  """

  def convert(filepath, body, _attrs, opts) do
    if Path.extname(filepath) in [".md", ".markdown"] do
      highlighters = Keyword.get(opts, :highlighters, [])

      body
      |> interpolate_placeholders()
      |> Earmark.as_html!()
      |> NimblePublisher.highlight(highlighters)
    end
  end

  @doc """
  Substitutes the supported placeholders in `body` with their
  compile-time values.
  """
  @spec interpolate_placeholders(String.t()) :: String.t()
  def interpolate_placeholders(body) when is_binary(body) do
    version = CureSite.cure_version()

    body
    |> String.replace("{{cure_version}}", version)
    |> String.replace("{{cure_vversion}}", "v" <> version)
  end
end
