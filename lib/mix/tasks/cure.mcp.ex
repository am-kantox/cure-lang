defmodule Mix.Tasks.Cure.Mcp do
  @moduledoc """
  Starts the Cure MCP (Model Context Protocol) server.

  The server communicates over stdio using newline-delimited JSON-RPC 2.0,
  compatible with any MCP client (Claude, Warp, etc.).

  ## Usage

      mix cure.mcp
  """

  use Mix.Task

  @shortdoc "Starts the Cure MCP server"

  @impl Mix.Task
  def run(_args) do
    Cure.MCP.Server.start()
  end
end
