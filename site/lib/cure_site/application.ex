defmodule CureSite.Application do
  # See https://hexdocs.pm/elixir/Application.html
  # for more information on OTP Applications
  @moduledoc false

  use Application

  @impl true
  def start(_type, _args) do
    warm_cure_stdlib()

    children = [
      CureSiteWeb.Telemetry,
      {DNSCluster, query: Application.get_env(:cure_site, :dns_cluster_query) || :ignore},
      {Phoenix.PubSub, name: CureSite.PubSub},
      # Start a worker by calling: CureSite.Worker.start_link(arg)
      # {CureSite.Worker, arg},
      # Start to serve requests, typically the last entry
      CureSiteWeb.Endpoint
    ]

    # See https://hexdocs.pm/elixir/Supervisor.html
    # for other strategies and supported options
    opts = [strategy: :one_for_one, name: CureSite.Supervisor]
    Supervisor.start_link(children, opts)
  end

  # Parse every stdlib `.cure` file exactly once at boot so the first
  # `:t Std.List.map` / `:doc Std.List` in the browser REPL does not
  # pay for lexing + parsing. The bundle is memoised in
  # `:persistent_term` by `Cure.Types.Stdlib.all/0`, so subsequent
  # callers just read the already-built map.
  #
  # The work is scheduled in an unlinked `Task` so a missing stdlib
  # (e.g. a broken release that stripped `priv/std/`) cannot prevent
  # the web endpoint from coming up; the REPL would simply report
  # "(no documentation source found)" the first time someone runs
  # `:doc Std.List`, which is already the documented fallback.
  defp warm_cure_stdlib do
    Task.start(fn ->
      try do
        _ = Cure.Types.Stdlib.all()
      rescue
        _ -> :ok
      end
    end)

    :ok
  end

  # Tell Phoenix to update the endpoint configuration
  # whenever the application is updated.
  @impl true
  def config_change(changed, _new, removed) do
    CureSiteWeb.Endpoint.config_change(changed, removed)
    :ok
  end
end
