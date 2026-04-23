defmodule CureSiteWeb.StdlibController do
  @moduledoc """
  Render the compile-time-extracted Cure standard library documentation.

  Two actions:

    * `:index` -- grid of modules, grouped via `CureSite.Stdlib.groups/0`.
    * `:show`  -- a single module page with sidebar + content pane.

  Both actions share the same left-hand navigation (module list +
  filter), so switching modules feels like ExDoc.
  """

  use CureSiteWeb, :controller

  alias CureSite.Stdlib

  def index(conn, _params) do
    conn
    |> assign(:page_title, "Standard Library")
    |> assign(:groups, Stdlib.groups())
    |> assign(:modules, Stdlib.modules())
    |> render(:index)
  end

  def show(conn, %{"module" => module}) do
    case Stdlib.module(module) do
      nil ->
        conn
        |> put_status(:not_found)
        |> put_view(html: CureSiteWeb.ErrorHTML)
        |> render("404.html")

      mod ->
        conn
        |> assign(:page_title, mod.module)
        |> assign(:groups, Stdlib.groups())
        |> assign(:modules, Stdlib.modules())
        |> assign(:module, mod)
        |> render(:show)
    end
  end
end
