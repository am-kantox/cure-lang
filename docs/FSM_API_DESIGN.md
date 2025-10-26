# Cure FSM API Design

This document describes the design of the Finite State Machine (FSM) API in Cure.

## Overview

FSMs in Cure are first-class language constructs that compile to BEAM processes. They provide:

- **Declarative state machine definitions** using Mermaid-style syntax
- **Custom payload types** (records or any Cure type)
- **Non-deterministic transitions** where handlers determine the next state
- **Process-based isolation** with message-passing semantics
- **Named FSM instances** for easy reference

## FSM Definition Syntax

```cure
module MyModule do
  # Define a payload record
  record MyPayload do
    field1: Type1
    field2: Type2
  end
  
  # Define FSM with initial payload
  fsm MyPayload{field1: initial_value1, field2: initial_value2} do
    State1 --> |event1| State2
    State1 --> |event2| State3
    State2 --> |event3| State1
    State2 --> |event3| State4  # Non-deterministic: same event, different target
  end
  
  # Define transition handlers
  def event1(from: StateName, event: Event, payload: MyPayload): Result(State, FsmError) =
    # Compute new state and payload
    Ok({:State2, updated_payload})
  
  def event2(from: StateName, event: Event, payload: MyPayload): Result(State, FsmError) =
    # Can return different states based on logic
    if some_condition then
      Ok({:State3, payload})
    else
      Error(:invalid_transition)
    end
end
```

## Core Types

```cure
# From Std.Fsm module
type FsmName = Atom                              # Registered FSM name
type FsmError = Atom                             # Error types (:invalid_state, etc.)
type EventName = Atom                            # Event identifier
type StateName = Atom                            # State identifier
type EventPayload = List(Pair(Atom, Any))        # Event-specific data
type Event = Pair(EventName, EventPayload)       # Event = {event_name, payload}
type State = Pair(StateName, Any)                # State = {state_name, fsm_payload}
```

## API Functions

### `start_fsm(module: Module): Pid`

Spawns a new FSM process with the FSM definition from the given module.

- **Initial state**: First state in the transition list
- **Initial payload**: Value specified in the `fsm` declaration
- **Returns**: Process ID (Pid) of the FSM instance

**Example:**
```cure
let fsm_pid = start_fsm(Turnstile)
```

### `fsm_cast(target: Pid | FsmName, event: Event): None`

Sends an event asynchronously to an FSM instance (fire-and-forget).

- **target**: Either a Pid or a registered FsmName
- **event**: Pair of `{event_name, event_payload}`
- **Returns**: None (asynchronous)

**Example:**
```cure
fsm_cast(fsm_pid, {:coin, []})
fsm_cast(:my_turnstile, {:push, [{:force, 100}]})
```

### `fsm_advertise(pid: Pid, name: FsmName): None`

Registers a name for an FSM process, allowing it to be referenced by name.

**Example:**
```cure
fsm_advertise(fsm_pid, :main_turnstile)
```

### `fsm_state(target: Pid | FsmName): Result(State, FsmError)`

Queries the current state and payload of an FSM instance.

- **Returns**: `Ok({state_name, payload})` or `Error(reason)`

**Example:**
```cure
match fsm_state(:main_turnstile) do
  Ok({state, payload}) ->
    println("Current state: " ++ show(state))
  Error(e) ->
    println("Error: " ++ show(e))
end
```

## Transition Handlers

Handlers are regular functions with a specific signature:

```cure
def handler_name(from: StateName, event: Event, payload: PayloadType): Result(State, FsmError)
```

**Parameters:**
- `from`: The current state name
- `event`: The event that triggered the transition (includes event name and data)
- `payload`: The current FSM payload

**Returns:**
- `Ok({next_state, new_payload})`: Successful transition with new state and payload
- `Error(reason)`: Transition failed with error reason

**Key Features:**
1. **Handler determines next state**: Multiple transitions with the same `from` state and event can exist
2. **Payload transformation**: Handler returns updated payload
3. **Conditional logic**: Can return different states based on payload or event data
4. **Error handling**: Can reject transitions by returning `Error`

## Non-Deterministic Transitions

The same state and event can transition to different target states based on handler logic:

```cure
fsm MyPayload{...} do
  Ready --> |check| Valid
  Ready --> |check| Invalid
  Ready --> |check| Pending
end

def check(from: StateName, event: Event, payload: MyPayload): Result(State, FsmError) =
  match payload.status do
    :complete -> Ok({:Valid, payload})
    :failed -> Ok({:Invalid, payload})
    :processing -> Ok({:Pending, payload})
    _ -> Error(:invalid_status)
  end
```

## Implementation Notes

### Process-Based FSM Runtime

- Each FSM instance runs as a separate BEAM process
- Events are sent as messages to the FSM process
- The process maintains the current state and payload
- Transition handlers are called within the FSM process context

### FSM Process Message Protocol

The FSM process should handle:
- `{:event, Event}`: Trigger a state transition
- `{:get_state, Pid}`: Query current state (reply to sender)
- `{:register, FsmName}`: Register a name for this FSM

### Compiler Responsibilities

The Cure compiler should:
1. Parse `fsm` blocks and extract transition table
2. Generate FSM definition structure with initial state/payload
3. Create transition map linking `{state, event}` to handler functions
4. Generate process spawning code that initializes FSM state
5. Implement message loop for handling events and state queries

## Complete Example: Turnstile

See `examples/turnstile.cure` for a complete working example demonstrating:
- Custom payload record
- Multiple state transitions
- Conditional payload updates
- FSM lifecycle (start, advertise, cast events, query state)

## Future Enhancements

Potential additions to the FSM API:
- `fsm_call/2`: Synchronous event sending with reply
- `fsm_stop/1`: Gracefully stop an FSM instance
- Timeout support: `State --> |timeout(1000)| NextState`
- State entry/exit actions
- FSM supervision trees
- FSM serialization/deserialization for persistence
