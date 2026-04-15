defmodule CureSiteWeb.BlogController do
  use CureSiteWeb, :controller

  alias CureSite.Blog

  def index(conn, _params) do
    conn
    |> assign(:page_title, "Blog")
    |> render(:index, posts: Blog.all_posts())
  end

  def show(conn, %{"id" => id}) do
    post = Blog.get_post_by_id!(id)

    conn
    |> assign(:page_title, post.title)
    |> render(:show, post: post)
  end
end
