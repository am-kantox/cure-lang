%{
  title: "Finite State Machines",
  description: "First-class FSMs with compile-time verification, struct-shaped state, caller/meta/payload separation, lifecycle hooks, event payloads, and transition notifications.",
  order: 4
}
---
FSMs are first-class language constructs in Cure. They are declaratively defined, verified at compile time for reachability and deadlock freedom, and -- in callback mode -- self-contained enough that the calling code only spawns an instance and sends events to it; everything else (state transitions, side effects, outbound notifications) lives with the `fsm` declaration.

Cure supports two compilation modes: **simple mode** (compiles to OTP `gen_statem`) and **callback mode** (compiles to a `GenServer` with inline `on_transition` handlers plus a full lifecycle, inspired by [Finitomata](https://hexdocs.pm/finitomata)).

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

The `@initial` annotation overrides the heuristic explicitly:

```cure
fsm DoorLock
  @initial :unlocked

  Locked   --unlock--> Unlocked
  Unlocked --lock-->   Locked
```

## The FSM state record: caller / meta / payload

Every callback-mode FSM stores its runtime state in a fixed record, `%Cure.FSM.State{}`, with three fields that serve distinct audiences:

- `:caller` -- the pid that spawned the FSM. Outbound notifications (`notify/1` inside callback bodies, the auto-notify path of `@notify_transitions`) are delivered here. Defaults to `nil`, which makes outbound messaging a safe no-op.
- `:meta` -- FSM-private bookkeeping. Read and written by lifecycle hooks; never exposed through `get_state/1`.
- `:payload` -- the user-visible domain value. Read by `Std.Fsm.get_state/1` and the compiled `get_state/1` API.

The record is the sole source of truth. Everything callers can observe from outside is either `:payload` or a message the FSM chose to send via `:caller`.

## Starting an FSM: three accepted init shapes

A generated FSM module exposes `start_link/0` and `start_link/1`. The 1-ary form accepts:

1. a pre-built `%Cure.FSM.State{}` struct -- used verbatim,
2. a keyword list or plain map with any of `:caller`, `:meta`, `:payload` -- lifted into the struct,
3. any other term -- treated as a bare `:payload` (so legacy callers that passed an initial data value keep working unchanged).

```elixir
alias Cure.FSM.State, as: FsmState

{:ok, pid} =
  :"Cure.FSM.Counter".start_link(%FsmState{
    caller: self(),
    meta: %{session: :test},
    payload: 0
  })

# or, equivalently:
{:ok, pid} =
  :"Cure.FSM.Counter".start_link(caller: self(), meta: %{session: :test}, payload: 0)

# or legacy:
{:ok, pid} = :"Cure.FSM.Counter".start_link(0)
```

When spawned via `Cure.FSM.Runtime.spawn_fsm/2` (or the Cure-level `Std.Fsm.spawn/1`), the spawning process is automatically recorded as the `:caller`, so notifications reach the expected pid without ceremony.

## Callback mode (on_transition)

When an `on_transition` block is present, the FSM compiles to a `GenServer`-based module. The transition graph and handler logic coexist in the same file:

```cure
fsm Turnstile with Integer
  Locked   --coin-->  Unlocked
  Unlocked --push-->  Locked
  Unlocked --coin-->  Unlocked
  Locked   --push-->  Locked

  on_transition
    (:locked, :coin, _payload, %{payload: n, meta: m}) ->
      %[:ok, :unlocked, %{payload: n + 1, meta: m}]
    (:unlocked, :push, _payload, %{payload: n, meta: m}) ->
      %[:ok, :locked, %{payload: n, meta: m}]
    (:unlocked, :coin, _payload, %{payload: n, meta: m}) ->
      %[:ok, :unlocked, %{payload: n + 1, meta: m}]
    (_, _, _, state) ->
      %[:ok, :__same__, state]
```

The `on_transition` clause head is `(current_state, event, event_payload, %FsmState{})`. Pattern-matching on the fourth arg as `%{payload: p, meta: m}` (a map pattern, since the struct is a map) is the idiomatic way to pull out the domain state.

Return values are normalised through `Cure.FSM.State.merge/2`:

- `%[:ok, next_state, %Cure.FSM.State{...}]` -- wholesale replacement of the struct,
- `%[:ok, next_state, %{payload: p, meta: m}]` -- partial merge; fields not mentioned survive,
- `%[:ok, next_state, bare_value]` -- bare value becomes the new `:payload`; `:caller` and `:meta` untouched (keeps v0.21.x FSMs source-compatible),
- `%[:ok, :__same__, ...]` -- stay in the current state,
- `%[:error, reason]` -- falls through to `on_failure`.

## Event payloads

Events may carry an arbitrary payload, threaded through to `on_transition` as the third argument:

```cure
mod MyApp
  fn push_with_source() -> Atom =
    let pid = Std.Fsm.spawn(:"Cure.FSM.Turnstile")
    Std.Fsm.send_with(pid, :coin, %{source: :token})
    Std.Fsm.state(pid)
```

The matching handler clause can destructure the event payload directly:

```cure
on_transition
  (:locked, :coin, %{source: :token}, state) ->
    %[:ok, :unlocked, state]
  (:locked, :coin, _, state) ->
    %[:error, :unknown_source]
```

## Notifying the outside world

Inside any lifecycle hook body, a bare `notify(message)` call reaches the FSM's `:caller`. At the Elixir level this compiles to `Cure.FSM.State.notify_self/1`, which reads the current-process registered state and sends the message. Outside an FSM process it is a no-op returning `:no_caller`.

```cure
on_transition
  (:ready, :process, payload, state) ->
    notify(%[:processed, payload])
    %[:ok, :done, state]
```

From Cure code, `Std.Fsm.notify(message)` is the same function, exposed explicitly for when you prefer the module-qualified call.

## Auto-notify via `@notify_transitions`

Opt into automatic transition notifications with the `@notify_transitions` annotation. After every successful transition (i.e. any `{:ok, next, _}` return that actually advances state), the FSM sends the caller:

```elixir
{:cure_fsm, fsm_pid, {:transition, from_state, event, to_state, new_payload}}
```

```cure
fsm Counter
  @notify_transitions

  Idle --inc--> Idle
  Idle --reset--> Idle

  on_transition
    (:idle, :inc,   _, %{payload: n, meta: m}) ->
      %[:ok, :idle, %{payload: n + 1, meta: m}]
    (:idle, :reset, _, %{payload: _, meta: m}) ->
      %[:ok, :idle, %{payload: 0, meta: m}]
    (_, _, _, state) -> %[:ok, :__same__, state]
```

The caller receives one message per transition:

```elixir
{:ok, pid} = :"Cure.FSM.Counter".start_link(caller: self(), payload: 0)
:"Cure.FSM.Counter".send_event(pid, :inc)

receive do
  {:cure_fsm, ^pid, {:transition, :idle, :inc, :idle, 1}} -> :ok
end
```

## Lifecycle callbacks

Optional callback blocks inside the FSM body (callback mode only). Each receives the struct as its last argument.

- `on_start` -- invoked inside `init/1`. Receives `(%FsmState{})`. May return `:ok`, `{:ok, %FsmState{...}}`, or `{:ok, %{payload: ..., meta: ...}}`. Use this for one-time setup and seeding initial state.
- `on_stop` -- invoked from `terminate/2`. Receives `(reason, %FsmState{})`. Use this for graceful cleanup.
- `on_enter` -- called after entering a state. Receives `(state_atom, %FsmState{})`.
- `on_exit` -- called before leaving a state. Receives `(state_atom, %FsmState{})`.
- `on_failure` -- called when a normal (non-soft) transition fails or the handler returns `{:error, reason}`. Receives `(event, event_payload, %FsmState{})`.
- `on_timer` -- called periodically when `@timer <ms>` is set. Receives `(state_atom, %FsmState{})`.

```cure
fsm Pipeline with Integer
  Idle    --start--> Ready
  Ready   --done-->  Finished

  on_start
    (state) ->
      notify(:fsm_started)
      %[:ok, state]

  on_transition
    (:idle, :start, _, %{payload: n, meta: m}) ->
      %[:ok, :ready, %{payload: n, meta: m}]
    (:ready, :done, _, state) ->
      notify(:fsm_finished)
      %[:ok, :finished, state]
    (_, _, _, state) -> %[:ok, :__same__, state]

  on_stop
    (_reason, _state) -> :ok
```

## Annotations

Annotations live at the top of the `fsm` block and configure behaviour at compile time.

- `@timer N` -- drive `on_timer` every `N` milliseconds.
- `@terminal State` -- mark a state as terminal (no outgoing transitions required for deadlock freedom).
- `@invariant expr` / `@verify expr` -- reserved for the verifier.
- `@initial :state_name` -- override the initial state (default: the first non-wildcard source).
- `@notify_transitions` -- auto-emit `{:cure_fsm, pid, {:transition, from, event, to, payload}}` to the caller after every successful transition.
- `@auto_caller` -- when `:caller` is not explicitly provided, fall back to the spawning process recorded in the FSM's process dictionary under `:cure_fsm_spawner`.

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

## Simple mode compilation

FSMs without `on_transition` compile to OTP `gen_statem` BEAM modules (the original behavior). Transitions can include inline `when` guards and `do` actions.

The compiler generates a BEAM module named after the FSM with a `Cure.FSM.` prefix. For `fsm TrafficLight`, the module is `:"Cure.FSM.TrafficLight"`.

## Generated API

Both compilation modes export:

- `start_link/0`, `start_link/1` -- start the FSM process. In callback mode `start_link/1` accepts the three init shapes documented above.
- `send_event/2` -- send a payload-less event (asynchronous cast).
- `send_event/3` (callback mode) -- send an event with a payload; the payload reaches `on_transition` as its third argument.
- `get_state/1` -- get the current `{state, payload}` (synchronous call). The caller sees only the `:payload` field, never the `:meta` or `:caller` fields.
- `get_fsm_state/1` (callback mode) -- get the current `{state, %Cure.FSM.State{}}`, exposing the full struct.
- `initial_state/0` (callback mode) -- return the initial state atom.
- `transitions/0` -- return the compiled transition table.
- `allowed/2` or `allowed?/2` -- check if a transition is valid.
- `responds?/2` (callback mode) -- check if an event is handled from a state.

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

- `spawn(module)` -- start an FSM process with the calling process recorded as the `:caller`; returns the pid.
- `spawn_with_payload(module, payload)` -- spawn with an explicit initial `:payload`.
- `spawn_with(module, init)` -- spawn with a fully-specified initial state. `init` may be a `%Cure.FSM.State{}` struct, a keyword list with `:caller`/`:meta`/`:payload`, or a plain map in the same shape.
- `spawn_named(module, name)` -- spawn and register under a string name for later lookup.
- `send(pid, event)` -- send a payload-less event.
- `send_with(pid, event, payload)` -- send an event carrying a payload; the payload reaches `on_transition` as its third argument.
- `send_batch(pid, events)` -- send a list of events in order.
- `state(pid)` -- get just the current state atom.
- `get_state(pid)` -- get `{state, payload}`.
- `full_state(pid)` -- get `{state, %Cure.FSM.State{}}` (the full struct).
- `caller(pid)` -- read the `:caller` pid registered for a running FSM.
- `notify(message)` -- from inside a lifecycle hook body, send `message` to the current FSM's `:caller`. A no-op returning `:no_caller` outside an FSM process.
- `history(pid)` -- get the recorded event history.
- `info(pid)` -- registry info for a running FSM.
- `is_alive(pid)` -- whether the FSM process is alive.
- `lookup(name)` -- look up a named FSM in the registry.
- `stop(pid)` -- stop the FSM process.

From Elixir, the equivalent is `Cure.FSM.Runtime`:

```elixir
alias Cure.FSM.State, as: FsmState

# Spawn with caller, meta, and payload in one shot
{:ok, pid} =
  Cure.FSM.Runtime.spawn_fsm(:"Cure.FSM.Counter",
    caller: self(),
    meta: %{session: :test},
    payload: 0
  )

# Or with a pre-built struct
{:ok, pid} =
  Cure.FSM.Runtime.spawn_fsm(:"Cure.FSM.Counter",
    init: %FsmState{caller: self(), meta: %{session: :test}, payload: 0}
  )

# Legacy :data still works; equivalent to payload:
{:ok, pid} = Cure.FSM.Runtime.spawn_fsm(:"Cure.FSM.Counter", data: 0)

# Register under a name
{:ok, pid} = Cure.FSM.Runtime.spawn_fsm(:"Cure.FSM.TrafficLight", name: "light1")

# Send events -- dispatch picks the right wire format per mode, so
# simple-mode gen_statem FSMs and callback-mode GenServer FSMs share
# the same API
Cure.FSM.Runtime.send_event(pid, :timer)
Cure.FSM.Runtime.send_event(pid, :coin, %{source: :token})

# Inspect state
{:ok, {:green, payload}} = Cure.FSM.Runtime.get_state(pid)
{:ok, {:green, %FsmState{caller: c, meta: m, payload: p}}} =
  Cure.FSM.Runtime.get_fsm_state(pid)

# Batch events (atoms or {event, payload} pairs)
Cure.FSM.Runtime.send_batch(pid, [:timer, {:coin, %{source: :token}}, :timer])

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

## Self-contained callback-mode example: turnstile with notifications

The turnstile example in `examples/cure_turnstile` puts the whole story together. The `.cure` file owns the transition graph, the coin count (in `:payload`), the passage count (in `:meta`), and opts into `@notify_transitions`:

```cure
fsm Turnstile with Integer
  Locked   --coin-->  Unlocked
  Unlocked --push-->  Locked
  Unlocked --coin-->  Unlocked
  Locked   --push-->  Locked

  @notify_transitions

  on_transition
    (:locked, :coin, _payload, %{payload: p, meta: m}) ->
      %[:ok, :unlocked, %{payload: p + 1, meta: m}]
    (:unlocked, :push, _payload, %{payload: p, meta: m}) ->
      %[:ok, :locked, %{payload: p, meta: %{passages: m.passages + 1}}]
    (:unlocked, :coin, _payload, %{payload: p, meta: m}) ->
      %[:ok, :unlocked, %{payload: p + 1, meta: m}]
    (_, _, _, state) ->
      %[:ok, :__same__, state]
```

The calling code is a thin facade: spawn, send events, read stats, optionally receive notifications:

```elixir
alias Cure.FSM.Runtime
alias Cure.FSM.State, as: FsmState

{:ok, pid} =
  Runtime.spawn_fsm(:"Cure.FSM.Turnstile",
    init: %FsmState{caller: self(), meta: %{passages: 0}, payload: 0}
  )

Runtime.send_event(pid, :coin)
Runtime.send_event(pid, :push)

receive do
  {:cure_fsm, ^pid, {:transition, :locked, :coin, :unlocked, 1}} -> :ok
end

{:ok, {state, %FsmState{payload: coins, meta: %{passages: p}}}} =
  Runtime.get_fsm_state(pid)
```

Everything else that used to live in a host-side wrapper GenServer (passage counting, state synchronisation, outbound events) now belongs to the FSM itself.
