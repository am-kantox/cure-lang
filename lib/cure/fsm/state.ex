defmodule Cure.FSM.State do
  @moduledoc """
  Runtime-state record shared by every Cure FSM instance.

  Every callback-mode FSM compiled from a `.cure` file carries a value of
  this shape as its primary state. The three fields serve distinct
  audiences:

    * `:caller`  -- the process that started the FSM. Outbound
      notifications from lifecycle hooks (`Std.Fsm.notify/1`,
      `@notify_transitions`) are delivered here. Defaults to `nil`, which
      makes outbound messaging a no-op.

    * `:meta` -- FSM-private bookkeeping. Lifecycle hooks are the only
      code that should read or write this field; it is never exposed via
      `get_state/1` to the outside world.

    * `:payload` -- the user-visible domain value. Readable through
      `Std.Fsm.get_state/1` and the compiled `get_state/1` API.

  An FSM's `start_link/1` accepts any of three initial shapes:

    1. a `%Cure.FSM.State{}` struct -- used verbatim;
    2. a keyword list or plain map containing `:caller`, `:meta`,
       `:payload` keys -- lifted into the struct;
    3. any other term -- treated as a legacy bare payload, i.e.
       `%Cure.FSM.State{payload: that_term}`.

  The struct is the sole source of truth for an FSM's runtime state.
  """

  @enforce_keys []
  defstruct caller: nil, meta: nil, payload: nil

  @type t :: %__MODULE__{
          caller: pid() | nil,
          meta: term(),
          payload: term()
        }

  @doc """
  Normalise any of the accepted init shapes into an `%FSM.State{}` struct.

  Accepts:

    * an existing `%Cure.FSM.State{}` struct (returned as-is),
    * a keyword list with any of `:caller`, `:meta`, `:payload`,
    * a map with any of those string or atom keys,
    * any other term -- treated as a bare `:payload`.
  """
  @spec from_init(term()) :: t()
  def from_init(%__MODULE__{} = state), do: state

  def from_init(kv) when is_list(kv) do
    if Keyword.keyword?(kv) do
      %__MODULE__{
        caller: Keyword.get(kv, :caller),
        meta: Keyword.get(kv, :meta),
        payload: Keyword.get(kv, :payload)
      }
    else
      %__MODULE__{payload: kv}
    end
  end

  def from_init(%{} = map) do
    get = fn key ->
      Map.get(map, key) || Map.get(map, Atom.to_string(key))
    end

    %__MODULE__{
      caller: get.(:caller),
      meta: get.(:meta),
      payload: get.(:payload)
    }
  end

  def from_init(other), do: %__MODULE__{payload: other}

  @doc """
  Apply a handler's partial return value on top of the current struct.

  The callback-mode FSM allows a user's `on_transition` clause to return
  any of:

    * `%Cure.FSM.State{}`  -- full replacement,
    * a map or keyword list containing `:payload` and/or `:meta`  --
      merged into the current struct,
    * any other term  -- treated as the new `:payload`, leaving
      `:caller` and `:meta` untouched.
  """
  @spec merge(t(), term()) :: t()
  def merge(%__MODULE__{} = _state, %__MODULE__{} = replacement), do: replacement

  def merge(%__MODULE__{} = state, %{} = partial) do
    has_payload = Map.has_key?(partial, :payload) or Map.has_key?(partial, "payload")
    has_meta = Map.has_key?(partial, :meta) or Map.has_key?(partial, "meta")

    if has_payload or has_meta do
      new_payload =
        if has_payload, do: Map.get(partial, :payload) || Map.get(partial, "payload"), else: state.payload

      new_meta =
        if has_meta, do: Map.get(partial, :meta) || Map.get(partial, "meta"), else: state.meta

      %__MODULE__{state | payload: new_payload, meta: new_meta}
    else
      %__MODULE__{state | payload: partial}
    end
  end

  def merge(%__MODULE__{} = state, kv) when is_list(kv) do
    if Keyword.keyword?(kv) do
      state
      |> maybe_put(:payload, kv)
      |> maybe_put(:meta, kv)
      |> maybe_put(:caller, kv)
    else
      %__MODULE__{state | payload: kv}
    end
  end

  def merge(%__MODULE__{} = state, bare), do: %__MODULE__{state | payload: bare}

  defp maybe_put(%__MODULE__{} = state, key, kv) do
    case Keyword.fetch(kv, key) do
      {:ok, v} -> Map.put(state, key, v)
      :error -> state
    end
  end

  @doc """
  Send `message` to `state.caller` if one is registered; otherwise no-op.

  Used by lifecycle hooks, `Std.Fsm.notify/1`, and the auto-notify path
  emitted when an FSM declares `@notify_transitions`.
  """
  @spec notify(t(), term()) :: term()
  def notify(%__MODULE__{caller: caller}, message) when is_pid(caller) do
    send(caller, message)
  end

  def notify(%__MODULE__{}, _message), do: :no_caller

  # -- Process-dictionary bridge ---------------------------------------------
  #
  # Callback bodies that wish to notify the caller without threading the
  # state struct through every function call use `Std.Fsm.notify/1`, which
  # resolves to `notify_self/1`. The owning process (the FSM GenServer)
  # stashes itself as `:cure_fsm_self` in its process dictionary on init,
  # so any code running inside the FSM can find the caller.

  @process_key :cure_fsm_state

  @doc false
  @spec register_self(t()) :: t()
  def register_self(%__MODULE__{} = state) do
    Process.put(@process_key, state)
    state
  end

  @doc false
  @spec current() :: t() | nil
  def current, do: Process.get(@process_key)

  @doc """
  Send `message` to the caller registered for the current FSM process, if
  any. Used by `Std.Fsm.notify/1`.
  """
  @spec notify_self(term()) :: term()
  def notify_self(message) do
    case current() do
      %__MODULE__{} = state -> notify(state, message)
      _ -> :no_caller
    end
  end
end
