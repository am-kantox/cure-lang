defmodule Cure.FSM.Runtime do
  @moduledoc """
  Runtime manager for Cure FSM instances.

  Provides a higher-level API on top of compiled `gen_statem` FSM modules:
  - Spawn and stop FSM instances with type tracking
  - ETS-backed registry for looking up running FSMs by name or pid
  - Batch event sending
  - Event history tracking
  - Process monitoring with automatic cleanup

  ## Usage

      # Start the runtime (done automatically via Application supervisor)
      Cure.FSM.Runtime.start_link()

      # Spawn an FSM instance
      {:ok, pid} = Cure.FSM.Runtime.spawn_fsm(:fsm_trafficlight, name: "traffic1")

      # Send events
      :ok = Cure.FSM.Runtime.send_event(pid, :timer)

      # Get state
      {:ok, {:green, %{}}} = Cure.FSM.Runtime.get_state(pid)

      # List running FSMs
      Cure.FSM.Runtime.list_fsms()

      # Stop
      :ok = Cure.FSM.Runtime.stop_fsm(pid)
  """

  use GenServer

  @registry_table :cure_fsm_registry

  # -- Public API --------------------------------------------------------------

  @doc "Start the FSM runtime manager."
  @spec start_link(keyword()) :: GenServer.on_start()
  def start_link(opts \\ []) do
    GenServer.start_link(__MODULE__, opts, name: __MODULE__)
  end

  @doc """
  Spawn a new FSM instance from a compiled FSM module.

  ## Options
  - `:name` -- optional string name for registry lookup
  - `:data` -- initial data (default: %{})
  """
  @spec spawn_fsm(module(), keyword()) :: {:ok, pid()} | {:error, term()}
  def spawn_fsm(fsm_module, opts \\ []) do
    GenServer.call(__MODULE__, {:spawn_fsm, fsm_module, opts})
  end

  @doc "Stop a running FSM instance."
  @spec stop_fsm(pid()) :: :ok | {:error, term()}
  def stop_fsm(pid) do
    GenServer.call(__MODULE__, {:stop_fsm, pid})
  end

  @doc "Send an event to an FSM instance."
  @spec send_event(pid(), term()) :: :ok
  def send_event(pid, event) do
    :gen_statem.cast(pid, event)
    GenServer.cast(__MODULE__, {:record_event, pid, event})
    :ok
  end

  @doc "Send a batch of events to an FSM instance."
  @spec send_batch(pid(), [term()]) :: :ok
  def send_batch(pid, events) do
    Enum.each(events, fn event ->
      :gen_statem.cast(pid, event)
    end)

    GenServer.cast(__MODULE__, {:record_batch, pid, events})
    :ok
  end

  @doc "Get the current state and data of an FSM instance."
  @spec get_state(pid()) :: {:ok, {atom(), term()}} | {:error, term()}
  def get_state(pid) do
    try do
      result = :gen_statem.call(pid, :get_state)
      {:ok, result}
    catch
      :exit, reason -> {:error, reason}
    end
  end

  @doc "Check if an FSM instance is alive."
  @spec alive?(pid()) :: boolean()
  def alive?(pid), do: Process.alive?(pid)

  @doc "Get info about a running FSM instance from the registry."
  @spec get_info(pid()) :: {:ok, map()} | :error
  def get_info(pid) do
    case :ets.lookup(@registry_table, pid) do
      [{^pid, info}] -> {:ok, info}
      [] -> :error
    end
  rescue
    ArgumentError -> :error
  end

  @doc "Look up an FSM by registered name."
  @spec lookup(String.t()) :: {:ok, pid()} | :error
  def lookup(name) do
    case :ets.match_object(@registry_table, {:_, %{name: name}}) do
      [{pid, _info}] -> {:ok, pid}
      _ -> :error
    end
  rescue
    ArgumentError -> :error
  end

  @doc "List all running FSM instances."
  @spec list_fsms() :: [map()]
  def list_fsms do
    :ets.tab2list(@registry_table)
    |> Enum.map(fn {pid, info} -> Map.put(info, :pid, pid) end)
  rescue
    ArgumentError -> []
  end

  @doc "Get the event history for an FSM instance."
  @spec event_history(pid()) :: [term()]
  def event_history(pid) do
    case get_info(pid) do
      {:ok, %{events: events}} -> Enum.reverse(events)
      _ -> []
    end
  end

  @doc """
  Get a health check report for an FSM instance.

  Returns a map with:
  - `:alive` -- whether the process is running
  - `:state` -- current FSM state (or `:unknown`)
  - `:event_count` -- total events processed
  - `:uptime_ms` -- milliseconds since spawn
  - `:last_event` -- most recent event (or nil)
  """
  @spec health_check(pid()) :: map()
  def health_check(pid) do
    is_alive = alive?(pid)

    state_info =
      if is_alive do
        case get_state(pid) do
          {:ok, {state, _data}} -> state
          _ -> :unknown
        end
      else
        :dead
      end

    info =
      case get_info(pid) do
        {:ok, info} -> info
        _ -> %{event_count: 0, started_at: 0, events: []}
      end

    now = System.monotonic_time(:millisecond)

    %{
      alive: is_alive,
      state: state_info,
      event_count: info.event_count,
      uptime_ms: now - Map.get(info, :started_at, now),
      last_event: List.first(info.events)
    }
  end

  # -- GenServer Callbacks -----------------------------------------------------

  @impl true
  def init(_opts) do
    table = :ets.new(@registry_table, [:set, :public, :named_table])
    {:ok, %{table: table}}
  end

  @impl true
  def handle_call({:spawn_fsm, fsm_module, opts}, _from, state) do
    name = Keyword.get(opts, :name)

    case fsm_module.start_link() do
      {:ok, pid} ->
        # Monitor the FSM process for automatic cleanup
        Process.monitor(pid)

        info = %{
          module: fsm_module,
          name: name,
          started_at: System.monotonic_time(:millisecond),
          events: [],
          event_count: 0
        }

        :ets.insert(@registry_table, {pid, info})
        {:reply, {:ok, pid}, state}

      {:error, reason} ->
        {:reply, {:error, reason}, state}
    end
  end

  def handle_call({:stop_fsm, pid}, _from, state) do
    :ets.delete(@registry_table, pid)

    try do
      :gen_statem.stop(pid)
      {:reply, :ok, state}
    catch
      :exit, _ -> {:reply, :ok, state}
    end
  end

  @impl true
  def handle_cast({:record_event, pid, event}, state) do
    case :ets.lookup(@registry_table, pid) do
      [{^pid, info}] ->
        # Keep last 100 events
        events = Enum.take([event | info.events], 100)
        updated = %{info | events: events, event_count: info.event_count + 1}
        :ets.insert(@registry_table, {pid, updated})

      [] ->
        :ok
    end

    {:noreply, state}
  end

  def handle_cast({:record_batch, pid, events}, state) do
    case :ets.lookup(@registry_table, pid) do
      [{^pid, info}] ->
        new_events = Enum.reverse(events) ++ info.events
        trimmed = Enum.take(new_events, 100)
        updated = %{info | events: trimmed, event_count: info.event_count + length(events)}
        :ets.insert(@registry_table, {pid, updated})

      [] ->
        :ok
    end

    {:noreply, state}
  end

  @impl true
  def handle_info({:DOWN, _ref, :process, pid, _reason}, state) do
    :ets.delete(@registry_table, pid)
    {:noreply, state}
  end

  def handle_info(_msg, state), do: {:noreply, state}
end
