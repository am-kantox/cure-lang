defmodule CureTurnstile do
  @moduledoc """
  A turnstile controller built on a Cure FSM.

  The state machine is defined in `cure_src/turnstile.cure` and compiled to
  `:\"Cure.FSM.Turnstile\"` -- a GenServer-based module using Cure's callback
  mode with an `on_transition` handler.

  The `on_transition` clauses handle coin counting:

      (:locked, :coin, _payload, data) -> {:ok, :unlocked, data + 1}

  This module wraps the FSM with passage counting on top.

  ## Quick Start

      {:ok, pid} = CureTurnstile.start_link()

      CureTurnstile.insert_coin(pid)
      # => :ok  (turnstile unlocks)

      CureTurnstile.push(pid)
      # => :ok  (person passes, turnstile locks)

      CureTurnstile.stats(pid)
      # => %{state: :locked, coins: 1, passages: 1}
  """

  use GenServer

  @fsm_module :"Cure.FSM.Turnstile"

  # -- Public API --------------------------------------------------------------

  @doc "Start a turnstile. The FSM begins in the `:locked` state with data `0`."
  @spec start_link(keyword()) :: GenServer.on_start()
  def start_link(opts \\ []) do
    GenServer.start_link(__MODULE__, opts, Keyword.take(opts, [:name]))
  end

  @doc "Insert a coin. Unlocks the turnstile (or keeps it unlocked if already open)."
  @spec insert_coin(GenServer.server()) :: :ok
  def insert_coin(pid), do: GenServer.call(pid, :coin)

  @doc "Push through the turnstile. Locks it after passage (no-op if already locked)."
  @spec push(GenServer.server()) :: :ok
  def push(pid), do: GenServer.call(pid, :push)

  @doc "Return the current FSM state atom (`:locked` or `:unlocked`)."
  @spec state(GenServer.server()) :: atom()
  def state(pid), do: GenServer.call(pid, :state)

  @doc "Return a stats map with `:state`, `:coins`, and `:passages`."
  @spec stats(GenServer.server()) :: map()
  def stats(pid), do: GenServer.call(pid, :stats)

  @doc "Check whether the turnstile is currently unlocked."
  @spec unlocked?(GenServer.server()) :: boolean()
  def unlocked?(pid), do: state(pid) == :unlocked

  # -- GenServer Callbacks -----------------------------------------------------

  @impl true
  def init(_opts) do
    {:ok, fsm_pid} = @fsm_module.start_link(0)
    {:ok, %{fsm: fsm_pid, passages: 0}}
  end

  @impl true
  def handle_call(:coin, _from, state) do
    @fsm_module.send_event(state.fsm, :coin)
    sync_fsm(state.fsm)
    {:reply, :ok, state}
  end

  def handle_call(:push, _from, state) do
    {old_state, _} = @fsm_module.get_state(state.fsm)

    @fsm_module.send_event(state.fsm, :push)
    sync_fsm(state.fsm)

    {new_state, _} = @fsm_module.get_state(state.fsm)

    passages =
      if old_state == :unlocked and new_state == :locked do
        state.passages + 1
      else
        state.passages
      end

    {:reply, :ok, %{state | passages: passages}}
  end

  def handle_call(:state, _from, state) do
    {fsm_state, _} = @fsm_module.get_state(state.fsm)
    {:reply, fsm_state, state}
  end

  def handle_call(:stats, _from, state) do
    {fsm_state, coins} = @fsm_module.get_state(state.fsm)
    {:reply, %{state: fsm_state, coins: coins, passages: state.passages}, state}
  end

  @impl true
  def terminate(_reason, state) do
    try do
      GenServer.stop(state.fsm)
    catch
      :exit, _ -> :ok
    end
  end

  # Sync: ensure the async cast has been processed
  defp sync_fsm(fsm_pid), do: _ = :sys.get_state(fsm_pid)
end
