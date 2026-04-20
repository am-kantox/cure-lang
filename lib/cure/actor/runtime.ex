defmodule Cure.Actor.Runtime do
  @moduledoc """
  Runtime manager for Cure actor instances.

  Provides a higher-level API on top of compiled actor `GenServer`
  modules, mirroring the FSM runtime:

    * Spawn and stop actor instances with caller tracking.
    * ETS-backed registry for lookup by name or pid.
    * Automatic cleanup on `DOWN` via process monitors.
    * List running actors for introspection.

  Started as a child of `Cure.Supervisor` by `Cure.Application`.
  """

  use GenServer

  alias Cure.Actor.State, as: ActorState

  @registry_table :cure_actor_registry

  # -- Public API --------------------------------------------------------------

  @doc "Start the actor runtime manager."
  @spec start_link(keyword()) :: GenServer.on_start()
  def start_link(opts \\ []) do
    GenServer.start_link(__MODULE__, opts, name: __MODULE__)
  end

  @doc """
  Spawn a new actor instance from a compiled actor module.

  ## Options
  - `:name`    -- optional string name for registry lookup
  - `:caller`  -- pid that receives outbound `notify/1` messages
                  (default: the spawning process)
  - `:payload` -- initial payload (overrides the actor's default)
  - `:meta`    -- actor-private metadata
  """
  @spec spawn_actor(module(), keyword()) :: {:ok, pid()} | {:error, term()}
  def spawn_actor(actor_module, opts \\ []) do
    GenServer.call(__MODULE__, {:spawn_actor, actor_module, opts, self()})
  end

  @doc "Stop a running actor instance."
  @spec stop_actor(pid()) :: :ok | {:error, term()}
  def stop_actor(pid) do
    GenServer.call(__MODULE__, {:stop_actor, pid})
  end

  @doc "Is the given pid alive?"
  @spec alive?(pid()) :: boolean()
  def alive?(pid), do: Process.alive?(pid)

  @doc "Look up an actor by registered name."
  @spec lookup(String.t()) :: {:ok, pid()} | :error
  def lookup(name) do
    case :ets.match_object(@registry_table, {:_, %{name: name}}) do
      [{pid, _info}] -> {:ok, pid}
      _ -> :error
    end
  rescue
    ArgumentError -> :error
  end

  @doc "Return info about a running actor."
  @spec get_info(pid()) :: {:ok, map()} | :error
  def get_info(pid) do
    case :ets.lookup(@registry_table, pid) do
      [{^pid, info}] -> {:ok, info}
      [] -> :error
    end
  rescue
    ArgumentError -> :error
  end

  @doc "List every running actor instance with its info."
  @spec list_actors() :: [map()]
  def list_actors do
    :ets.tab2list(@registry_table)
    |> Enum.map(fn {pid, info} -> Map.put(info, :pid, pid) end)
  rescue
    ArgumentError -> []
  end

  # -- GenServer callbacks -----------------------------------------------------

  @impl true
  def init(_opts) do
    table = :ets.new(@registry_table, [:set, :public, :named_table])
    {:ok, %{table: table}}
  end

  @impl true
  def handle_call({:spawn_actor, actor_module, opts, spawner}, _from, state) do
    init_arg = build_init_arg(opts, spawner)

    case actor_module.start_link(init_arg) do
      {:ok, pid} ->
        Process.monitor(pid)

        info = %{
          module: actor_module,
          name: Keyword.get(opts, :name),
          caller: caller_from_init(init_arg),
          started_at: System.monotonic_time(:millisecond)
        }

        :ets.insert(@registry_table, {pid, info})
        {:reply, {:ok, pid}, state}

      {:error, reason} ->
        {:reply, {:error, reason}, state}
    end
  end

  def handle_call({:stop_actor, pid}, _from, state) do
    :ets.delete(@registry_table, pid)

    try do
      GenServer.stop(pid)
      {:reply, :ok, state}
    catch
      :exit, _ -> {:reply, :ok, state}
    end
  end

  @impl true
  def handle_info({:DOWN, _ref, :process, pid, _reason}, state) do
    :ets.delete(@registry_table, pid)
    {:noreply, state}
  end

  def handle_info(_msg, state), do: {:noreply, state}

  # -- Helpers -----------------------------------------------------------------

  defp build_init_arg(opts, spawner) do
    cond do
      Keyword.has_key?(opts, :init) ->
        Keyword.fetch!(opts, :init)

      Keyword.has_key?(opts, :caller) or Keyword.has_key?(opts, :payload) or
          Keyword.has_key?(opts, :meta) ->
        %ActorState{
          caller: Keyword.get(opts, :caller, spawner),
          meta: Keyword.get(opts, :meta),
          payload: Keyword.get(opts, :payload)
        }

      true ->
        %ActorState{caller: spawner}
    end
  end

  defp caller_from_init(%ActorState{caller: c}), do: c
  defp caller_from_init(_), do: nil
end
