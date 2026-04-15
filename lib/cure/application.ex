defmodule Cure.Application do
  @moduledoc false

  use Application

  @impl Application
  def start(_type, _args) do
    # Start the protocol registry ETS table
    Cure.Types.ProtocolRegistry.start()

    children = [
      {Registry, keys: :duplicate, name: Cure.Pipeline.Events.Registry},
      Cure.FSM.Runtime
    ]

    opts = [strategy: :one_for_one, name: Cure.Supervisor]
    Supervisor.start_link(children, opts)
  end
end
