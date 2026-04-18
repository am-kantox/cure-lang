defmodule CureSiteWeb.PageControllerTest do
  use CureSiteWeb.ConnCase

  test "GET / renders the home page with the dynamic Cure version", %{conn: conn} do
    conn = get(conn, ~p"/")
    body = html_response(conn, 200)

    # Hero copy that identifies the Cure home page.
    assert body =~
             "Dependently-typed programming language for the BEAM virtual machine"

    # Version is injected from the top-level mix.exs at compile time and
    # rendered both in the navbar badge and in the hero blurb.
    version = CureSite.cure_version()
    assert body =~ "v" <> version

    # Top-level nav entries after the Types/Dependent merge.
    assert body =~ ~r{>\s*Types\s*<}
    assert body =~ ~r{>\s*Match\s*<}

    # The separate "Dependent" nav entry and its "new" badge were folded
    # into the Types page -- neither should appear as a standalone link.
    refute body =~ ~r{<a[^>]*>\s*Dependent}
    refute body =~ ~s(badge-accent">new</span>)
  end
end
