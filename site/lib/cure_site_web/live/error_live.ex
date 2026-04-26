defmodule CureSiteWeb.ErrorLive do
  @moduledoc """
  LiveView rendered on HTTP error pages (404, 5xx).

  Embeds a Yeesh terminal pre-loaded with the `CureEval` command so visitors
  can experiment with Cure code while they work out where they meant to go.
  """

  use CureSiteWeb, :live_view

  @impl true
  def mount(params, session, socket) do
    raw = session["error_status"] || params["status"]

    status =
      case raw do
        nil -> nil
        s when is_integer(s) -> s
        s when is_binary(s) -> String.to_integer(s)
        _ -> nil
      end

    json_ld =
      if status,
        do: CureSiteWeb.JsonLd.for_error(status),
        else: CureSiteWeb.JsonLd.for_repl()

    {:ok,
     socket
     |> assign(:page_title, if(status, do: error_title(status), else: "Cure REPL"))
     |> assign(:json_ld, json_ld)
     |> assign(:status, status)}
  end

  @impl true
  def render(assigns) do
    ~H"""
    <Layouts.app flash={@flash}>
      <div class="flex flex-col items-center gap-8 py-8">
        <%!-- Hero image (only on actual error pages) ---%>
        <%= if @status do %>
          <div class="relative w-full max-w-2xl overflow-hidden rounded-2xl shadow-2xl">
            <img
              src={error_image(@status)}
              alt={"Error #{@status}"}
              class="w-full object-cover"
              style="max-height: 340px; object-position: center;"
            />
            <div class="absolute inset-0 flex flex-col items-center justify-center bg-black/50 p-6 text-center">
              <p class="text-8xl font-black text-white drop-shadow">{@status}</p>
              <p class="mt-2 text-xl font-semibold text-white/90 drop-shadow">
                {error_message(@status)}
              </p>
              <a
                href="/"
                class="mt-4 rounded-lg bg-white/20 px-4 py-2 text-sm font-medium text-white backdrop-blur hover:bg-white/30 transition"
              >
                Back to home
              </a>
            </div>
          </div>
        <% else %>
          <div class="text-center space-y-2">
            <h1 class="text-3xl font-bold tracking-tight">Cure REPL</h1>
            <p class="text-base-content/60 text-sm">
              Browser-based access to the Cure language. Type
              <code class="rounded bg-base-300 px-1 py-0.5 font-mono text-xs">repl</code>
              for a full interactive session,
              <code class="rounded bg-base-300 px-1 py-0.5 font-mono text-xs">eval 1 + 1</code>
              for a one-shot expression, or
              <code class="rounded bg-base-300 px-1 py-0.5 font-mono text-xs">help</code>
              to list available commands.
            </p>
          </div>
        <% end %>

        <%!-- Yeesh terminal ---%>
        <div class="w-full max-w-4xl">
          <p class="mb-3 text-sm text-base-content/60 text-center">
            While you're here, try the Cure REPL.
            Type <code class="rounded bg-base-300 px-1 py-0.5 font-mono text-xs">repl</code>
            to start a full interactive session,
            <code class="rounded bg-base-300 px-1 py-0.5 font-mono text-xs">eval 1 + 1</code>
            for a one-shot expression, or
            <code class="rounded bg-base-300 px-1 py-0.5 font-mono text-xs">help</code>
            to list commands.
          </p>
          <div
            id="error-terminal-container"
            class="w-full overflow-hidden rounded-xl shadow-2xl border border-base-300"
            style="height: 420px;"
          >
            <.live_component
              module={Yeesh.Live.TerminalComponent}
              id="error-terminal"
              commands={[
                CureSiteWeb.Commands.CureRepl,
                CureSiteWeb.Commands.CureEval
              ]}
              prompt="cure> "
              theme={:default}
              welcome_message={
                "\e[1;36mCure REPL\e[0m -- " <>
                  "type \e[1mrepl\e[0m for an interactive session, " <>
                  "\e[1meval <expr>\e[0m for a one-shot expression, " <>
                  "\e[1mhelp\e[0m for the command list."
              }
            />
          </div>
          <div class="mt-3 flex flex-wrap gap-2 justify-center text-xs text-base-content/40">
            <span class="rounded-full bg-base-200 px-2 py-1">Tab: autocomplete</span>
            <span class="rounded-full bg-base-200 px-2 py-1">Up/Down: history</span>
            <span class="rounded-full bg-base-200 px-2 py-1">Ctrl+C: interrupt</span>
            <span class="rounded-full bg-base-200 px-2 py-1">Ctrl+L: clear</span>
          </div>
        </div>
      </div>
    </Layouts.app>
    """
  end

  # ---------------------------------------------------------------------------

  defp error_title(404), do: "404 Not Found"
  defp error_title(status), do: "#{status} Error"

  defp error_message(404), do: "Page not found"
  defp error_message(500), do: "Internal server error"
  defp error_message(503), do: "Service unavailable"
  defp error_message(status), do: "Something went wrong (#{status})"

  defp error_image(404), do: ~p"/images/404.jpg"
  defp error_image(_), do: ~p"/images/500.jpg"
end
