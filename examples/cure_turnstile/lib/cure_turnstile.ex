defmodule CureTurnstile do
  @moduledoc """
  A turnstile controlled by a first-class Cure FSM.

  The entire controller lives in `cure_src/turnstile.cure`, which
  declares the transition graph, counts coins through the `:payload`
  field, and counts passages through the `:meta` field. It also turns on
  `@notify_transitions`, so every successful transition reaches the
  process that spawned the FSM as

      {:cure_fsm, fsm_pid, {:transition, from, event, to, payload}}

  This Elixir module is now a thin facade: there is no wrapper
  GenServer, no `:sys.get_state/1` sync, no host-side bookkeeping. It
  just spawns the FSM, forwards events, and reads `{state, payload}`
  when asked for stats.

  ## Quick Start

      {:ok, pid} = CureTurnstile.start_link()

      CureTurnstile.insert_coin(pid)
      CureTurnstile.push(pid)

      CureTurnstile.stats(pid)
      # => %{state: :locked, coins: 1, passages: 1}

  ## Listening for transitions

  Because the FSM is spawned with the calling process as its `:caller`,
  `receive`ing in the caller will pick up every transition. See the test
  suite for the exact shape.
  """

  alias Cure.FSM.State, as: FsmState
  alias Cure.FSM.Runtime

  @fsm_module :"Cure.FSM.Turnstile"

  @doc """
  Start a turnstile FSM. The initial `:payload` is `0` (coins) and the
  initial `:meta` is `%{passages: 0}`.

  The spawning process is recorded as the FSM's `:caller`; lifecycle
  hooks reach it via `Std.Fsm.notify/1`, and -- because the `.cure`
  file opts in with `@notify_transitions` -- every completed
  transition sends a message to it.
  """
  @spec start_link() :: {:ok, pid()} | {:error, term()}
  def start_link do
    Runtime.spawn_fsm(@fsm_module,
      init: %FsmState{caller: self(), meta: %{passages: 0}, payload: 0}
    )
  end

  @doc "Insert a coin. Delivered as an event; the FSM advances asynchronously."
  @spec insert_coin(pid()) :: :ok
  def insert_coin(pid) do
    Runtime.send_event(pid, :coin)
    sync(pid)
    :ok
  end

  @doc "Push through the turnstile. Delivered as an event."
  @spec push(pid()) :: :ok
  def push(pid) do
    Runtime.send_event(pid, :push)
    sync(pid)
    :ok
  end

  @doc "Stop the turnstile."
  @spec stop(pid()) :: :ok
  def stop(pid), do: Runtime.stop_fsm(pid)

  @doc "Return the current FSM state atom (`:locked` or `:unlocked`)."
  @spec state(pid()) :: atom()
  def state(pid) do
    {current, _payload} = @fsm_module.get_state(pid)
    current
  end

  @doc "Return a stats map with `:state`, `:coins`, and `:passages`."
  @spec stats(pid()) :: map()
  def stats(pid) do
    {current, %FsmState{payload: coins, meta: meta}} = @fsm_module.get_fsm_state(pid)
    passages = if is_map(meta), do: Map.get(meta, :passages, 0), else: 0
    %{state: current, coins: coins, passages: passages}
  end

  @doc "Check whether the turnstile is currently unlocked."
  @spec unlocked?(pid()) :: boolean()
  def unlocked?(pid), do: state(pid) == :unlocked

  # The FSM processes events asynchronously (`GenServer.cast`); `sync/1`
  # blocks until the event has been handled so callers can immediately
  # read the resulting state.
  defp sync(pid), do: _ = :sys.get_state(pid)
end
