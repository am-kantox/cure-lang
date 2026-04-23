defmodule CureMotif.MidiOut do
  @moduledoc """
  In-memory MIDI event sink.

  The Cure `Sequencer` actor uses `notify(...)` after every `:tick`
  message, which sends the notification to whatever process started
  the actor (the "caller"). The sequencer is started by this module's
  `start_link/1`, so every `%[:event, e]` notification lands in this
  Agent's mailbox; `handle_info/2` forwards it into a bounded event log.

  This is the Elixir side of the Cure showcase's hear-and-see-it loop:
  running `CureMotif.demo/0` populates the log, and
  `CureMotif.PianoRoll.render/1` renders that log as ASCII.

  The log has a capped size (default 4096 entries) so long-running
  demos never consume unbounded memory.
  """

  use GenServer

  @default_cap 4096

  # -- Public API ------------------------------------------------------------

  @doc """
  Start the sink under a supervisor. Registered by default as
  `#{inspect(__MODULE__)}`.
  """
  @spec start_link(keyword()) :: GenServer.on_start()
  def start_link(opts \\ []) do
    GenServer.start_link(__MODULE__, opts, Keyword.put_new(opts, :name, __MODULE__))
  end

  @doc "Clear the event log."
  @spec reset() :: :ok
  def reset, do: GenServer.call(__MODULE__, :reset)

  @doc "Return the event log in insertion order (oldest first)."
  @spec events() :: [term()]
  def events, do: GenServer.call(__MODULE__, :events)

  @doc "Return the number of events currently in the log."
  @spec count() :: non_neg_integer()
  def count, do: GenServer.call(__MODULE__, :count)

  @doc "Manually append an event to the log."
  @spec push(term()) :: :ok
  def push(event), do: GenServer.cast(__MODULE__, {:push, event})

  # -- GenServer callbacks ---------------------------------------------------

  @impl true
  def init(opts) do
    cap = Keyword.get(opts, :cap, @default_cap)
    {:ok, %{events: [], cap: cap}}
  end

  @impl true
  def handle_call(:reset, _from, state) do
    {:reply, :ok, %{state | events: []}}
  end

  def handle_call(:events, _from, state) do
    {:reply, Enum.reverse(state.events), state}
  end

  def handle_call(:count, _from, state) do
    {:reply, length(state.events), state}
  end

  @impl true
  def handle_cast({:push, event}, state) do
    {:noreply, %{state | events: cap_push(state.events, event, state.cap)}}
  end

  @impl true
  def handle_info({:event, event}, state) do
    # Cure's `notify(%[:event, e])` becomes an Erlang `{:event, e}` message.
    {:noreply, %{state | events: cap_push(state.events, event, state.cap)}}
  end

  def handle_info([:event, event], state) do
    # Fall-back for list-shaped messages.
    {:noreply, %{state | events: cap_push(state.events, event, state.cap)}}
  end

  def handle_info(_msg, state), do: {:noreply, state}

  # -- Helpers ---------------------------------------------------------------

  defp cap_push(events, event, cap) do
    # Cons onto the front, truncate the oldest tail when over cap.
    [event | Enum.take(events, cap - 1)]
  end
end
