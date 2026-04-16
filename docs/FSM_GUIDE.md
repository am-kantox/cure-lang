# FSM Programming Guide

## Defining FSMs

FSMs are first-class language constructs in Cure:

```cure
fsm TrafficLight
  Red    --timer-->     Green
  Green  --timer-->     Yellow
  Yellow --timer-->     Red
  *      --emergency--> Red
```

Each line defines a transition: `SourceState --event--> TargetState`.

The `*` wildcard matches any source state.

## Two Compilation Modes

### Simple mode (no `on_transition`)

FSMs without an `on_transition` block compile to OTP `gen_statem` BEAM modules.
This is the original, backward-compatible behavior. Transitions can include
inline `when` guards and `do` actions.

### Callback mode (`on_transition` present)

FSMs with an `on_transition` block compile to a `GenServer`-based module.
The transition graph and the handler logic coexist in the same file,
inspired by Finitomata.

```cure
fsm Turnstile with Integer
  Locked   --coin-->  Unlocked
  Unlocked --push-->  Locked
  Unlocked --coin-->  Unlocked
  Locked   --push-->  Locked

  on_transition
    (:locked, :coin, _payload, data) -> %[:ok, :unlocked, data + 1]
    (:unlocked, :push, _payload, data) -> %[:ok, :locked, data]
    (_, _, _, data) -> %[:ok, :__same__, data]
```

The `on_transition` clauses receive `(current_state, event, event_payload, state_payload)`
and return `%[:ok, next_state, new_payload]` or `%[:error, reason]`.
Return `:__same__` as next_state to stay in the current state.

## Event Suffixes (Finitomata-inspired)

### Hard events (`event!`)

A `!`-suffixed event auto-fires when the FSM enters a state where that
event is the sole outgoing event:

```cure
fsm Pipeline
  Idle    --start-->   Setup
  Setup   --init!-->   Ready
  Ready   --process--> Done
```

After entering `Setup`, the `init!` event fires automatically via
`{:continue, ...}`. The compiler verifies that hard events are the sole
outgoing event from their source state.

### Soft events (`event?`)

A `?`-suffixed event silently fails without logging or calling
`on_failure`:

```cure
fsm Poller
  Active --poll?-->  Active
  Active --done-->   Finished
```

If `poll?` fails, the FSM stays in its current state without noise.

## Lifecycle Callbacks

Optional callback blocks inside the FSM body:

- `on_enter` -- called after entering a state
- `on_exit` -- called before leaving a state
- `on_failure` -- called when a normal (non-soft) transition fails
- `on_timer` -- called periodically when `@timer <ms>` is set

```cure
fsm MyFSM
  Idle --go--> Active
  Active --done--> Idle
  @timer 5000

  on_enter
    (:active, _state) -> :ok

  on_timer
    (:active, state) -> {:ok, state.payload}
```

## Generated API

Both modes export:

- `start_link/0`, `start_link/1` -- start the FSM process
- `send_event/2` -- send an event (cast)
- `get_state/1` -- get current `{state, data}` (synchronous call)
- `transitions/0` -- return the compiled transition table
- `allowed/2` (simple) / `allowed?/2` (callback) -- check if a transition is valid
- `responds?/2` (callback) -- check if an event is handled from a state

## Compile-Time Verification

The compiler automatically verifies:

1. **Reachability**: every state is reachable from the initial state (BFS)
2. **Deadlock freedom**: every non-terminal state has outgoing transitions
3. **Terminal state validation**: declared terminal states exist in the graph
4. **Hard event validation**: `!` events must be the sole outgoing event
5. **Ambiguous transition warnings**: when `on_transition` is present, warns about
   events that can lead to multiple target states

## Using FSMs at Runtime

With the FSM runtime (`Cure.FSM.Runtime`):

```elixir
# Spawn an FSM
{:ok, pid} = Cure.FSM.Runtime.spawn_fsm(:"Cure.FSM.TrafficLight", name: "light1")

# Send events
Cure.FSM.Runtime.send_event(pid, :timer)

# Get state
{:ok, {:green, %{}}} = Cure.FSM.Runtime.get_state(pid)

# Batch events
Cure.FSM.Runtime.send_batch(pid, [:timer, :timer, :timer])

# Query transition tables
Cure.FSM.Runtime.allowed?(:"Cure.FSM.TrafficLight", :red, :timer)
Cure.FSM.Runtime.responds?(:"Cure.FSM.TrafficLight", :red, :timer)

# Registry lookup
{:ok, pid} = Cure.FSM.Runtime.lookup("light1")

# Stop
Cure.FSM.Runtime.stop_fsm(pid)
```

## From Cure Code

Using the `Std.Fsm` stdlib module:

```cure
mod MyApp
  fn run_light() -> Atom =
    let pid = Std.Fsm.spawn(:"Cure.FSM.TrafficLight")
    Std.Fsm.send(pid, :timer)
    let state = Std.Fsm.state(pid)
    Std.Fsm.stop(pid)
    state
```

## Initial State

The first non-wildcard source state in the definition becomes the
initial state. In the traffic light example, `Red` is the initial state.

## Wildcard Transitions

`* --event--> Target` creates a transition from every state to `Target`
when `event` is received. Useful for emergency/reset transitions.
