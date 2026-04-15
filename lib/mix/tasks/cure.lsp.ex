defmodule Mix.Tasks.Cure.Lsp do
  @moduledoc """
  Starts the Cure Language Server Protocol server.

  The server communicates over stdio using JSON-RPC 2.0 with
  Content-Length framing, compatible with any LSP client.

  ## Usage

      mix cure.lsp
  """

  use Mix.Task

  @shortdoc "Starts the Cure LSP server"

  @impl Mix.Task
  def run(_args) do
    Mix.Task.run("app.start", [])

    {:ok, _pid} = Cure.LSP.Server.start_link()

    # Keep the process alive
    Process.sleep(:infinity)
  end
end
