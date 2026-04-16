defmodule CureSiteWeb.Layouts do
  @moduledoc """
  This module holds layouts and related functionality
  used by your application.
  """
  use CureSiteWeb, :html

  # Embed all files in layouts/* within this module.
  # The default root.html.heex file contains the HTML
  # skeleton of your application, namely HTML headers
  # and other static content.
  embed_templates "layouts/*"

  @doc """
  Renders your app layout.

  This function is typically invoked from every template,
  and it often contains your application menu, sidebar,
  or similar.

  ## Examples

      <Layouts.app flash={@flash}>
        <h1>Content</h1>
      </Layouts.app>

  """
  attr :flash, :map, required: true, doc: "the map of flash messages"

  attr :current_scope, :map,
    default: nil,
    doc: "the current [scope](https://hexdocs.pm/phoenix/scopes.html)"

  slot :inner_block, required: true

  def app(assigns) do
    ~H"""
    <header class="sticky top-0 z-50 border-b border-base-300 bg-base-100/95 backdrop-blur">
      <nav class="mx-auto flex max-w-5xl items-center justify-between px-4 py-3 sm:px-6">
        <a href="/" class="flex items-center gap-2">
          <img src={~p"/images/logo-128x128-nobg.png"} width="32" height="32" alt="Cure" />
          <span class="text-lg font-bold tracking-tight">Cure</span>
          <span class="text-xs text-base-content/50">v0.15.0</span>
        </a>

        <div class="hidden items-center gap-1 md:flex">
          <a href={~p"/language-guide"} class="btn btn-ghost btn-sm">Language</a>
          <a href={~p"/type-system"} class="btn btn-ghost btn-sm">Types</a>
          <a href={~p"/finite-state-machines"} class="btn btn-ghost btn-sm">FSMs</a>
          <a href={~p"/protocols"} class="btn btn-ghost btn-sm">Protocols</a>
          <a href={~p"/standard-library"} class="btn btn-ghost btn-sm">Stdlib</a>
          <a href={~p"/tooling"} class="btn btn-ghost btn-sm">Tooling</a>
          <a href={~p"/blog"} class="btn btn-ghost btn-sm">Blog</a>
          <.theme_toggle />
        </div>

        <%!-- Mobile menu button --%>
        <div class="flex items-center gap-2 md:hidden">
          <.theme_toggle />
          <button
            class="btn btn-ghost btn-sm"
            onclick="document.getElementById('mobile-menu').classList.toggle('hidden')"
          >
            <.icon name="hero-bars-3" class="size-5" />
          </button>
        </div>
      </nav>

      <%!-- Mobile navigation --%>
      <div id="mobile-menu" class="hidden border-t border-base-300 px-4 py-2 md:hidden">
        <a href={~p"/language-guide"} class="block py-2 text-sm">Language Guide</a>
        <a href={~p"/type-system"} class="block py-2 text-sm">Type System</a>
        <a href={~p"/finite-state-machines"} class="block py-2 text-sm">Finite State Machines</a>
        <a href={~p"/protocols"} class="block py-2 text-sm">Protocols</a>
        <a href={~p"/standard-library"} class="block py-2 text-sm">Standard Library</a>
        <a href={~p"/tooling"} class="block py-2 text-sm">Tooling</a>
        <a href={~p"/roadmap"} class="block py-2 text-sm">Roadmap</a>
        <a href={~p"/blog"} class="block py-2 text-sm">Blog</a>
      </div>
    </header>

    <main class="mx-auto max-w-4xl px-4 py-10 sm:px-6 lg:px-8">
      {render_slot(@inner_block)}
    </main>

    <footer class="border-t border-base-300 mt-16">
      <div class="mx-auto max-w-5xl px-4 py-8 sm:px-6">
        <div class="flex flex-col items-center justify-between gap-4 sm:flex-row">
          <div class="flex items-center gap-4 text-sm text-base-content/60">
            <a href="https://github.com/am-kantox/cure-lang" class="hover:text-base-content">GitHub</a>
            <a href={~p"/getting-started"} class="hover:text-base-content">Getting Started</a>
            <a href={~p"/roadmap"} class="hover:text-base-content">Roadmap</a>
          </div>
          <p class="text-xs text-base-content/40">Cure v0.15.0 -- Aleksei Matiushkin</p>
        </div>
      </div>
    </footer>

    <.flash_group flash={@flash} />
    """
  end

  @doc """
  Shows the flash group with standard titles and content.

  ## Examples

      <.flash_group flash={@flash} />
  """
  attr :flash, :map, required: true, doc: "the map of flash messages"
  attr :id, :string, default: "flash-group", doc: "the optional id of flash container"

  def flash_group(assigns) do
    ~H"""
    <div id={@id} aria-live="polite">
      <.flash kind={:info} flash={@flash} />
      <.flash kind={:error} flash={@flash} />
    </div>
    """
  end

  @doc """
  Provides dark vs light theme toggle based on themes defined in app.css.

  See <head> in root.html.heex which applies the theme before page load.
  """
  def theme_toggle(assigns) do
    ~H"""
    <div class="card relative flex flex-row items-center border-2 border-base-300 bg-base-300 rounded-full">
      <div class="absolute w-1/3 h-full rounded-full border-1 border-base-200 bg-base-100 brightness-200 left-0 [[data-theme=light]_&]:left-1/3 [[data-theme=dark]_&]:left-2/3 transition-[left]" />

      <button
        class="flex p-2 cursor-pointer w-1/3"
        data-phx-theme="system"
      >
        <.icon name="hero-computer-desktop-micro" class="size-4 opacity-75 hover:opacity-100" />
      </button>

      <button
        class="flex p-2 cursor-pointer w-1/3"
        data-phx-theme="light"
      >
        <.icon name="hero-sun-micro" class="size-4 opacity-75 hover:opacity-100" />
      </button>

      <button
        class="flex p-2 cursor-pointer w-1/3"
        data-phx-theme="dark"
      >
        <.icon name="hero-moon-micro" class="size-4 opacity-75 hover:opacity-100" />
      </button>
    </div>
    """
  end
end
