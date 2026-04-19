defmodule CureMoneta.Application do
  @moduledoc false

  use Application

  @impl true
  def start(_type, _args) do
    children = [
      CureMoneta.LedgerServer,
      {DynamicSupervisor, name: CureMoneta.TxSupervisor, strategy: :one_for_one}
    ]

    opts = [strategy: :one_for_all, name: CureMoneta.Supervisor]
    Supervisor.start_link(children, opts)
  end
end
