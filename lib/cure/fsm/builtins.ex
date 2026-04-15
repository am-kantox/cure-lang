defmodule Cure.FSM.Builtins do
  @moduledoc """
  Built-in FSM functions callable from Cure programs via `@extern`.

  These bridge the gap between Cure code and the FSM runtime,
  providing the FFI functions that `Std.Fsm` delegates to.
  """

  alias Cure.FSM.Runtime

  @doc "Spawn an FSM instance from its module atom. Returns pid or {:error, reason}."
  def fsm_spawn(module_atom) do
    case Runtime.spawn_fsm(module_atom) do
      {:ok, pid} -> pid
      {:error, reason} -> {:error, reason}
    end
  end

  @doc "Spawn a named FSM instance."
  def fsm_spawn_named(module_atom, name) do
    case Runtime.spawn_fsm(module_atom, name: name) do
      {:ok, pid} -> pid
      {:error, reason} -> {:error, reason}
    end
  end

  @doc "Stop an FSM instance."
  def fsm_stop(pid), do: Runtime.stop_fsm(pid)

  @doc "Send an event to an FSM."
  def fsm_send(pid, event), do: Runtime.send_event(pid, event)

  @doc "Send a batch of events."
  def fsm_send_batch(pid, events), do: Runtime.send_batch(pid, events)

  @doc "Get the current state of an FSM. Returns {state, data} or {:error, reason}."
  def fsm_get_state(pid) do
    case Runtime.get_state(pid) do
      {:ok, result} -> result
      {:error, reason} -> {:error, reason}
    end
  end

  @doc "Get just the state atom."
  def fsm_state(pid) do
    case Runtime.get_state(pid) do
      {:ok, {state, _data}} -> state
      {:error, reason} -> {:error, reason}
    end
  end

  @doc "Check if an FSM is alive."
  def fsm_is_alive(pid), do: Runtime.alive?(pid)

  @doc "Get FSM info from the registry."
  def fsm_info(pid) do
    case Runtime.get_info(pid) do
      {:ok, info} -> info
      :error -> {:error, :not_found}
    end
  end

  @doc "Get event history."
  def fsm_history(pid), do: Runtime.event_history(pid)

  @doc "Look up an FSM by name."
  def fsm_lookup(name) do
    case Runtime.lookup(name) do
      {:ok, pid} -> pid
      :error -> {:error, :not_found}
    end
  end
end
