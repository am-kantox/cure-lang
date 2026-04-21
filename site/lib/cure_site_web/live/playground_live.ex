defmodule CureSiteWeb.PlaygroundLive do
  @moduledoc """
  Cure Playground LiveView (v0.27.0).

  A browser-side playground for exploring Cure syntax. The current
  iteration of the playground uses `Makeup.Lexers.CureLexer` to
  render the user's input with syntax highlighting -- the same
  highlighter the REPL uses for its live display. Future releases
  will add on-the-fly type checking once the compiler core is
  factored out into a sandboxed library (see `docs/PLAYGROUND.md`).
  """

  use CureSiteWeb, :live_view

  alias Makeup.Registry

  @impl true
  def mount(_params, _session, socket) do
    source = default_source()
    highlighted = highlight(source)

    {:ok,
     socket
     |> assign(:page_title, "Cure Playground")
     |> assign(:source, source)
     |> assign(:highlighted, highlighted)
     |> assign(:form, to_form(%{"source" => source}, as: "playground"))}
  end

  @impl true
  def handle_event(
        "update",
        %{"playground" => %{"source" => source}},
        socket
      ) do
    {:noreply,
     socket
     |> assign(:source, source)
     |> assign(:highlighted, highlight(source))
     |> assign(:form, to_form(%{"source" => source}, as: "playground"))}
  end

  # -- Internals --------------------------------------------------------------

  defp default_source do
    """
    mod Demo
      fn add(a: Int, b: Int) -> Int = a + b

      fn doubled(xs: List(Int)) -> List(Int) =
        xs |> Std.List.map(fn (x) -> x * 2)
    """
  end

  defp highlight(source) when is_binary(source) do
    case Registry.fetch_lexer_by_name("cure") do
      {:ok, {lexer, opts}} ->
        source
        |> lexer.lex(opts)
        |> Makeup.Formatters.HTML.HTMLFormatter.format_as_iolist([])
        |> IO.iodata_to_binary()

      :error ->
        # Fallback: escape HTML so the browser treats the source as text.
        Phoenix.HTML.html_escape(source) |> Phoenix.HTML.safe_to_string()
    end
  rescue
    _ ->
      Phoenix.HTML.html_escape(source) |> Phoenix.HTML.safe_to_string()
  end

  @impl true
  def render(assigns) do
    ~H"""
    <Layouts.app flash={@flash}>
      <main class="mx-auto max-w-5xl p-6">
        <h1 class="text-3xl font-bold mb-4">Cure Playground</h1>

        <p class="text-gray-600 mb-6">
          Edit the Cure source below. The preview re-renders on every
          keystroke via the same <code>Makeup.Lexers.CureLexer</code>
          that powers the REPL's live syntax highlighter.
        </p>

        <.form
          for={@form}
          id="playground-form"
          phx-change="update"
          class="grid grid-cols-1 md:grid-cols-2 gap-6"
        >
          <div>
            <label class="block text-sm font-semibold mb-2">Source</label>
            <.input
              field={@form[:source]}
              type="textarea"
              rows="20"
              class="w-full h-96 font-mono text-sm border rounded p-3"
              phx-debounce="150"
            />
          </div>

          <div>
            <label class="block text-sm font-semibold mb-2">Highlighted</label>
            <pre class="w-full h-96 font-mono text-sm border rounded p-3 overflow-auto bg-gray-50"><code class="makeup">{Phoenix.HTML.raw(@highlighted)}</code></pre>
          </div>
        </.form>

        <p class="mt-8 text-sm text-gray-500">
          Type-checking and in-browser evaluation are on the roadmap
          for v0.28. See
          <.link navigate={~p"/roadmap"} class="underline">the roadmap</.link>
          for details.
        </p>
      </main>
    </Layouts.app>
    """
  end
end
