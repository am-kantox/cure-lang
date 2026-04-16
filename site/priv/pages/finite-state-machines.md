%{
  title: "Finite State Machines",
  description: "First-class FSMs with compile-time verification, dual-mode compilation, event suffixes, and inline transition handlers.",
  order: 4
}
---
FSMs are first-class language constructs in Cure. They define state machines declaratively and are verified at compile time for reachability and deadlock freedom. Cure supports two compilation modes: **simple mode** (compiles to OTP `gen_statem`) and **callback mode** (compiles to `GenServer` with inline `on_transition` handlers, inspired by [Finitomata](https://hexdocs.pm/finitomata)).

## Defining FSMs

Use `fsm` followed by a name. Each line in the body defines a transition: `SourceState --event--> TargetState`.

```cure
fsm TrafficLight
  Red    --timer-->     Green
  Green  --timer-->     Yellow
  Yellow --timer-->     Red
  *      --emergency--> Red
```

This defines a traffic light with three states (`Red`, `Green`, `Yellow`) and two events (`timer`, `emergency`).

## Wildcard transitions

The `*` wildcard matches any source state. It creates a transition from every state to the target when that event is received:

```cure
*  --emergency--> Red
```

This means: from `Red`, `Green`, or `Yellow`, receiving `emergency` transitions to `Red`. Useful for reset and panic transitions.

## Initial state

The first non-wildcard source state in the definition becomes the initial state. In the traffic light example above, `Red` is the initial state because it appears first as a source.

```cure
fsm DoorLock
  Locked   --unlock--> Unlocked
  Unlocked --lock-->   Locked
  Unlocked --open-->   Open
  Open     --close-->  Unlocked
# Initial state: Locked (first non-wildcard source)
```

## Callback mode (on_transition)

When an `on_transition` block is present, the FSM compiles to a `GenServer`-based module. The transition graph and handler logic coexist in the same file:

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

The `on_transition` clauses receive `(current_state, event, event_payload, state_payload)` and return `%[:ok, next_state, new_payload]` or `%[:error, reason]`. Return `:__same__` as next_state to stay in the current state.

## Event suffixes

### Hard events (`event!`)

A `!`-suffixed event auto-fires when the FSM enters a state where that event is the sole outgoing event:

```cure
fsm Pipeline
  Idle    --start-->   Setup
  Setup   --init!-->   Ready
  Ready   --process--> Done
```

After entering `Setup`, the `init!` event fires automatically. The compiler verifies that hard events are the sole outgoing event from their source state.

### Soft events (`event?`)

A `?`-suffixed event silently fails without logging or calling `on_failure`:

```cure
fsm Poller
  Active --poll?-->  Active
  Active --done-->   Finished
```

If `poll?` fails, the FSM stays in its current state without noise.

## Lifecycle callbacks

Optional callback blocks inside the FSM body (callback mode only):

- `on_enter` -- called after entering a state
- `on_exit` -- called before leaving a state
- `on_failure` -- called when a normal (non-soft) transition fails
- `on_timer` -- called periodically when `@timer <ms>` is set

## Simple mode compilation

FSMs without `on_transition` compile to OTP `gen_statem` BEAM modules (the original behavior). Transitions can include inline `when` guards and `do` actions.

The compiler generates a BEAM module named after the FSM with a `Cure.FSM.` prefix. For `fsm TrafficLight`, the module is `:"Cure.FSM.TrafficLight"`.

## Generated API

Both compilation modes export:

- `start_link/0`, `start_link/1` -- start the FSM process
- `send_event/2` -- send an event to an FSM process (asynchronous cast)
- `get_state/1` -- get the current `{state, data}` (synchronous call)
- `transitions/0` -- return the compiled transition table
- `allowed/2` or `allowed?/2` -- check if a transition is valid
- `responds?/2` (callback mode) -- check if an event is handled from a state

Usage from Elixir:

```elixir
{:ok, pid} = :"Cure.FSM.TrafficLight".start_link()
:"Cure.FSM.TrafficLight".send_event(pid, :timer)
{:green, %{}} = :"Cure.FSM.TrafficLight".get_state(pid)
```

## Compile-time verification

The FSM compiler (`Cure.FSM.Verifier`) automatically checks:

1. **Reachability**: every state is reachable from the initial state (BFS)
2. **Deadlock freedom**: every non-terminal state has outgoing transitions
3. **Terminal state validation**: declared terminal states exist in the graph
4. **Hard event validation**: `!` events must be the sole outgoing event from their state
5. **Ambiguous transition warnings**: warns when the same event from a state leads to multiple targets (requires `on_transition` to resolve)

Example that triggers a reachability warning:

```cure
fsm Broken
  A --go--> B
  C --go--> D
# Warning: states C, D are unreachable from initial state A
```

## Guards on transitions

Transitions can have `when` guards that restrict when they fire. The guard expression is compiled to Erlang guard sequences on the `handle_event` clause:

```cure
fsm Counter
  Counting --tick when count > 0--> Counting
  Counting --tick when count == 0--> Done
```

The guard has access to the FSM's state data. In this example, `count` is a field in the state data map. The transition from `Counting` to `Counting` only fires when `count > 0`; when `count` reaches 0, the FSM transitions to `Done`.

## Actions on transitions

Transitions can include `do` blocks that mutate state data during the transition:

```cure
fsm Counter
  Counting --tick when count > 0 do count = count - 1--> Counting
  Counting --tick when count == 0--> Done
```

The `do` expression compiles to code in the `handle_event` clause body. The action has access to the current state data and returns modified data. In this example, each `tick` event decrements `count` by 1.

## Full counter FSM example

A complete FSM with guards, actions, and multiple states:

```cure
fsm Counter
  Counting --tick when count > 0 do count = count - 1--> Counting
  Counting --tick when count == 0--> Done
  *        --reset--> Counting
```

This FSM:

- Starts in `Counting` state
- On each `tick`, decrements `count` if it is positive
- Transitions to `Done` when `count` reaches 0
- Can be reset from any state back to `Counting` via the `reset` event

Compiled gen_statem behavior: the `start_link/1` function accepts initial data (e.g., `%{count: 5}`), and each transition clause pattern-matches on the event atom and applies guards/actions accordingly.

## Runtime API via Std.Fsm

From Cure code, use the `Std.Fsm` stdlib module to interact with FSMs:

```cure
mod MyApp
  fn run_light() -> Atom =
    let pid = Std.Fsm.spawn(:"Cure.FSM.TrafficLight")
    Std.Fsm.send(pid, :timer)
    let state = Std.Fsm.state(pid)
    Std.Fsm.stop(pid)
    state
```

Available functions in `Std.Fsm`:

- `spawn(module)` -- start an FSM process, returns the pid
- `send(pid, event)` -- send an event to the FSM
- `state(pid)` -- get the current state
- `history(pid)` -- get the event history
- `lookup(name)` -- look up a named FSM in the registry
- `stop(pid)` -- stop the FSM process

From Elixir, the equivalent is `Cure.FSM.Runtime`:

```elixir
# Spawn with a registered name
{:ok, pid} = Cure.FSM.Runtime.spawn_fsm(:"Cure.FSM.TrafficLight", name: "light1")

# Send events
Cure.FSM.Runtime.send_event(pid, :timer)

# Get state
{:ok, {:green, %{}}} = Cure.FSM.Runtime.get_state(pid)

# Batch events
Cure.FSM.Runtime.send_batch(pid, [:timer, :timer, :timer])

# Event history
Cure.FSM.Runtime.event_history(pid)

# Registry lookup by name
{:ok, pid} = Cure.FSM.Runtime.lookup("light1")

# Stop
Cure.FSM.Runtime.stop_fsm(pid)
```

## Health check API

The FSM Runtime provides a health check endpoint for monitoring:

```elixir
{:ok, health} = Cure.FSM.Runtime.health_check(pid)
# Returns:
# %{
#   alive: true,
#   state: :green,
#   event_count: 42,
#   uptime_ms: 15000,
#   last_event: :timer
# }
```

This is useful for supervision, dashboards, and operational monitoring of long-running FSM processes.

## Type safety analysis

The compiler performs static analysis on FSM definitions to catch common errors:

### Duplicate transitions

Two transitions with the same source state and event (without guards to disambiguate) produce a warning:

```cure
fsm Bad
  A --go--> B
  A --go--> C
# Warning: duplicate transition from A on event 'go'
```

With guards, the same source/event pair is allowed because the guards disambiguate:

```cure
fsm Ok
  A --go when x > 0--> B
  A --go when x <= 0--> C
# No warning: guards make the transitions distinct
```

### Wildcard shadows

If a wildcard transition and an explicit transition handle the same event, the explicit transition takes precedence. The compiler warns when a wildcard completely shadows an unreachable explicit transition:

```cure
fsm Shadowed
  A --go--> B
  * --go--> C
# The wildcard creates transitions from all states on 'go',
# but A --go--> B takes precedence for state A.
# Warning if B --go--> C is never reachable due to shadowing.
```

### Self-loops

A transition from a state to itself is valid but flagged as informational when combined with no action (it has no observable effect):

```cure
fsm Loop
  A --noop--> A
# Info: self-loop on state A with event 'noop' (no action)
```

With an action, self-loops are meaningful and produce no diagnostic:

```cure
fsm Counter
  Counting --tick do count = count + 1--> Counting
# No warning: self-loop has an action
```

## Complete example

A door lock FSM with guards, actions, and multiple events:

```cure
fsm DoorLock
  Locked   --enter_code when code == secret do attempts = 0--> Unlocked
  Locked   --enter_code when code != secret do attempts = attempts + 1--> Locked
  Locked   --enter_code when attempts >= 3--> Blocked
  Unlocked --lock-->   Locked
  Unlocked --open-->   Open
  Open     --close-->  Unlocked
  Blocked  --admin_reset--> Locked
  *        --emergency_open--> Open
```

This FSM:

- Starts `Locked`
- Accepts a code; if correct, unlocks and resets attempts; if wrong, increments attempts
- Blocks after 3 failed attempts
- Can be admin-reset from `Blocked`
- Has an emergency override from any state
- Compile-time verified: all states reachable, no deadlocks, terminal states valid
