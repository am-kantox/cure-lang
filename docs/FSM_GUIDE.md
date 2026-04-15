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

## Compilation

FSMs compile to OTP `gen_statem` BEAM modules:

```bash
cure compile traffic_light.cure
```

The generated module provides:
- `start_link/0`, `start_link/1` -- start the FSM process
- `send_event/2` -- send an event (cast)
- `get_state/1` -- get current state (synchronous call)

## Compile-Time Verification

The compiler automatically verifies:

1. **Reachability**: every state is reachable from the initial state (BFS)
2. **Deadlock freedom**: every non-terminal state has outgoing transitions
3. **Terminal state validation**: declared terminal states exist in the graph

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

# Event history
Cure.FSM.Runtime.event_history(pid)

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
