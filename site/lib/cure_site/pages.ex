defmodule CureSite.Pages do
  alias CureSite.Pages.Page

  use NimblePublisher,
    build: Page,
    from: Application.app_dir(:cure_site, "priv/pages/**/*.md"),
    as: :pages,
    highlighters: [:makeup_cure, :makeup_elixir, :makeup_erlang],
    html_converter: CureSite.MarkdownConverter

  @pages Enum.sort_by(@pages, & &1.order)

  def all_pages, do: @pages

  def nav_pages do
    Enum.filter(all_pages(), &(&1.order > 0))
  end

  defmodule NotFoundError do
    defexception [:message, plug_status: 404]
  end

  def get_page_by_id!(id) do
    Enum.find(all_pages(), &(&1.id == id)) ||
      raise NotFoundError, "page with id=#{id} not found"
  end
end
