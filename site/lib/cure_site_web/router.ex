defmodule CureSiteWeb.Router do
  use CureSiteWeb, :router

  pipeline :browser do
    plug :accepts, ["html"]
    plug :fetch_session
    plug :fetch_live_flash
    plug :put_root_layout, html: {CureSiteWeb.Layouts, :root}
    plug :protect_from_forgery
    plug :put_secure_browser_headers
  end

  pipeline :api do
    plug :accepts, ["json"]
  end

  # Chrome DevTools probes this path; return 204 to silence the error.
  scope "/.well-known" do
    get "/*path", CureSiteWeb.WellKnownController, :noop
  end

  scope "/", CureSiteWeb do
    pipe_through :browser

    get "/", PageController, :home
    get "/blog", BlogController, :index
    get "/blog/:id", BlogController, :show
    get "/:id", PageController, :show
  end

  # Other scopes may use custom stacks.
  # scope "/api", CureSiteWeb do
  #   pipe_through :api
  # end
end
