defmodule CureSiteWeb.PageController do
  use CureSiteWeb, :controller

  alias CureSiteWeb.JsonLd

  def home(conn, _params) do
    conn
    |> assign(:json_ld, JsonLd.for_home(CureSite.cure_version()))
    |> render(:home)
  end

  def show(conn, %{"id" => id}) do
    page = CureSite.Pages.get_page_by_id!(id)

    conn
    |> assign(:page_title, page.title)
    |> assign(:json_ld, JsonLd.for_page(page))
    |> render(:show, page: page)
  end
end
