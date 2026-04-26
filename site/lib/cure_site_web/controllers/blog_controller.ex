defmodule CureSiteWeb.BlogController do
  use CureSiteWeb, :controller

  alias CureSite.Blog
  alias CureSiteWeb.JsonLd

  def index(conn, _params) do
    posts = Blog.all_posts()

    conn
    |> assign(:page_title, "Blog")
    |> assign(:json_ld, JsonLd.for_blog_index(posts))
    |> render(:index, posts: posts)
  end

  def show(conn, %{"id" => id}) do
    post = Blog.get_post_by_id!(id)

    conn
    |> assign(:page_title, post.title)
    |> assign(:json_ld, JsonLd.for_blog_post(post))
    |> render(:show, post: post)
  end
end
