defmodule CureSiteWeb.ErrorHTMLTest do
  use CureSiteWeb.ConnCase, async: true

  test "404 error page embeds ErrorLive" do
    {_status, _headers, body} =
      assert_error_sent(404, fn ->
        get(build_conn(), "/this-path-does-not-exist")
      end)

    # Root layout wraps the live_render placeholder.
    assert body =~ "<html"
    assert body =~ "data-phx-session"
  end
end
