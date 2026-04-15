defmodule CureSiteWeb.PageController do
  use CureSiteWeb, :controller

  def home(conn, _params) do
    render(conn, :home)
  end

  def show(conn, %{"id" => id}) do
    page = CureSite.Pages.get_page_by_id!(id)

    conn
    |> assign(:page_title, page.title)
    |> render(:show, page: page)
  end
end
