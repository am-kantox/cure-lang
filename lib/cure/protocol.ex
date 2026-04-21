defmodule Cure.Protocol do
  @moduledoc """
  Top-level entry point for Cure's session-typed `protocol` container
  (v0.27.0).

  Combines `Cure.Protocol.Parser`, `Cure.Protocol.Script`, and
  `Cure.Protocol.Verifier` into a single fluent API.

  ## Example

      iex> dsl = \"""
      ...> protocol Ping.Pong with Client, Server
      ...>   Client -> Server: Ping
      ...>   Server -> Client: Pong(Int)
      ...>   end
      ...> \"""
      iex> {:ok, script} = Cure.Protocol.parse(dsl)
      iex> Cure.Protocol.verify(script)
      :ok

  ## Integration with actors

  An actor can declare a role via the `@protocol` decorator on its
  container (future Cure-surface work). At the runtime level,
  `Cure.Protocol.Verifier.participant_trace/2` returns the projected
  FSM-like model ready for temporal reasoning via
  `Cure.Temporal.Checker`.
  """

  alias Cure.Protocol.{Parser, Script, Verifier}

  defdelegate parse(dsl), to: Parser
  defdelegate verify(script), to: Verifier
  defdelegate participant_trace(script, role), to: Verifier
  defdelegate project(script, role), to: Script

  @doc """
  Convenience: parse and verify a DSL in one call.

  Returns `{:ok, script}` on a successful parse *and* verify, or
  `{:error, reason}` at the first failing stage.
  """
  @spec parse_and_verify(String.t()) :: {:ok, Script.t()} | {:error, term()}
  def parse_and_verify(dsl) when is_binary(dsl) do
    with {:ok, script} <- parse(dsl),
         :ok <- verify(script) do
      {:ok, script}
    end
  end
end
