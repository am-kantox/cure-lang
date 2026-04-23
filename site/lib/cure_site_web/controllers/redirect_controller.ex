defmodule CureSiteWeb.RedirectController do
  @moduledoc """
  Permanent redirects for URLs that moved.

  The `/standard-library` route was a monolithic hand-written page.
  v0.28.x replaced it with an auto-generated `/stdlib` area backed by
  `CureSite.Stdlib`; this redirect keeps any external links alive.
  """

  use CureSiteWeb, :controller

  def to_stdlib(conn, _params) do
    conn
    |> put_status(:moved_permanently)
    |> redirect(to: ~p"/stdlib")
  end
end
