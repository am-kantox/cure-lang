defmodule CureSiteWeb.WellKnownController do
  use CureSiteWeb, :controller

  def noop(conn, _params) do
    send_resp(conn, 204, "")
  end
end
