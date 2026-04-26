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
  alias CureSiteWeb.JsonLd

  def index(conn, _params) do
    modules = Stdlib.modules()

    conn
    |> assign(:page_title, "Standard Library")
    |> assign(:groups, Stdlib.groups())
    |> assign(:modules, modules)
    |> assign(:json_ld, JsonLd.for_stdlib_index(modules))
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
        |> assign(:json_ld, JsonLd.for_stdlib_module(mod))
        |> render(:show)
    end
  end
end
