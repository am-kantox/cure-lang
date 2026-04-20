defmodule Cure.Actor.Builtins do
  @moduledoc """
  Built-in actor functions callable from Cure programs via `@extern`.

  These bridge the gap between Cure code and the actor runtime,
  providing the FFI functions that `Std.Actor` delegates to.
  """

  alias Cure.Actor.Runtime

  @doc "Spawn an actor from its compiled module atom."
  def actor_spawn(actor_module) do
    case Runtime.spawn_actor(actor_module) do
      {:ok, pid} -> pid
      {:error, reason} -> {:error, reason}
    end
  end

  @doc "Spawn an actor with an initial payload."
  def actor_spawn_with_payload(actor_module, payload) do
    case Runtime.spawn_actor(actor_module, payload: payload) do
      {:ok, pid} -> pid
      {:error, reason} -> {:error, reason}
    end
  end

  @doc "Spawn a named actor."
  def actor_spawn_named(actor_module, name) do
    case Runtime.spawn_actor(actor_module, name: name) do
      {:ok, pid} -> pid
      {:error, reason} -> {:error, reason}
    end
  end

  @doc "Stop a running actor."
  def actor_stop(pid), do: Runtime.stop_actor(pid)

  @doc """
  Send a message to an actor via the Melquiades operator's semantics
  (Erlang's `!`). Returns the sent message.
  """
  def actor_send(pid, msg) do
    send(pid, msg)
    msg
  end

  @doc "Fetch the actor's current payload via its `get_state/1` call."
  def actor_get_state(pid) do
    try do
      mod = actor_module_of(pid)
      if mod, do: mod.get_state(pid), else: nil
    catch
      :exit, _ -> {:error, :dead}
    end
  end

  @doc "Is this actor pid still alive?"
  def actor_is_alive(pid), do: Runtime.alive?(pid)

  @doc "Look up a named actor."
  def actor_lookup(name) do
    case Runtime.lookup(name) do
      {:ok, pid} -> pid
      :error -> {:error, :not_found}
    end
  end

  defp actor_module_of(pid) do
    case Runtime.get_info(pid) do
      {:ok, %{module: mod}} -> mod
      _ -> nil
    end
  end
end
