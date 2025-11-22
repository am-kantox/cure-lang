# Cure FSM API Design

**Last Updated**: November 22, 2025

This document describes the design of the Finite State Machine (FSM) API in Cure.

## Overview

FSMs in Cure are first-class language constructs that compile to BEAM `gen_statem` processes. They provide:

- **Declarative state machine definitions** using arrow-based transition syntax
- **Record-based payload types** for carrying data through transitions
- **Simple event-driven transitions** between states
- **Process-based isolation** with BEAM message-passing semantics
- **Named FSM instances** for easy reference via atoms

## FSM Definition Syntax

Cure FSMs use a simple, declarative syntax:

```cure
module MyModule do
  # Define a payload record to track FSM data
  record MyPayload do
    field1: Type1
    field2: Type2
  end
  
  # Define FSM with initial payload values
  fsm MyPayload{field1: initial_value1, field2: initial_value2} do
    State1 --> |event1| State2
    State1 --> |event2| State3
    State2 --> |event3| State1
  end
end
```

**Key Points**:
- The first state in the transition list is the initial state
- States are capitalized atoms (`:State1`, `:State2`, etc.)
- Events are lowercase atoms enclosed in `|event|` syntax
- Each FSM must have an associated record type for the payload
- The record fields are initialized in the `fsm` declaration

## Core Types

From the `Std.Fsm` module:

```cure
type FsmName = Atom       # Registered FSM name (e.g., :traffic_light)
type FsmError = Atom      # Error types (:invalid_state, :not_found, etc.)
type EventName = Atom     # Event identifier (e.g., :timer, :coin)
type StateName = Atom     # State identifier (e.g., :Red, :Green)
```

## API Functions

### `start_fsm(module: Atom): Pid`

Spawns a new FSM process using the FSM definition from the given module.

- **Initial state**: First state in the transition list
- **Initial payload**: Values specified in the `fsm` declaration
- **Returns**: Process ID (Pid) of the FSM instance

**Example:**
```cure
# This would start the FSM defined in the TrafficLightFSM module
let fsm_pid = start_fsm(:TrafficLightFSM)
```

**Note**: This is a legacy function. The recommended approach is `fsm_spawn/2`.

### `fsm_cast(target: Any, event: Any): Any`

Sends an event asynchronously to an FSM instance (fire-and-forget).

- **target**: Either a Pid or a registered FsmName (atom)
- **event**: A Pair containing `(event_name, event_data)` where event_data is a list
- **Returns**: Cast result (typically `ok`)

**Example:**
```cure
import Std.Pair [pair/2]

# Send event with empty data
let empty_list = []
let event = pair(:coin, empty_list)
fsm_cast(fsm_pid, event)

# Or to a named FSM
let event2 = pair(:push, [])
fsm_cast(:my_turnstile, event2)
```

### `fsm_advertise(pid: Any, name: Atom): Any`

Registers a name for an FSM process, allowing it to be referenced by name instead of Pid.

**Example:**
```cure
let adv_result = fsm_advertise(fsm_pid, :main_turnstile)
# Now you can use :main_turnstile instead of fsm_pid
```

### `fsm_state(target: Any): Any`

Queries the current state of an FSM instance.

- **Returns**: Current state atom (e.g., `:Red`, `:Locked`)

**Example:**
```cure
let current_state = fsm_state(:traffic_light)
# Returns atom like :Red, :Green, or :Yellow
```

### `fsm_spawn(fsm_type: Atom, initial_data: Any): Any`

Spawns an FSM instance with a specific type and initial data.

- **fsm_type**: The FSM type atom (matches the payload record name)
- **initial_data**: Initial payload data (usually a record instance)
- **Returns**: Process ID (Pid) of the spawned FSM

**Example:**
```cure
let initial_data = TrafficPayload{cycles_completed: 0, timer_events: 0, emergency_stops: 0}
let fsm_pid = fsm_spawn(:TrafficPayload, initial_data)
```

## Additional API Functions

### `fsm_stop(pid: Any): Any`

Gracefully stops an FSM instance.

**Example:**
```cure
fsm_stop(fsm_pid)
```

### `fsm_info(pid: Any): Any`

Get detailed information about an FSM instance including state, data, and event history.

**Example:**
```cure
let info = fsm_info(fsm_pid)
```

### `fsm_is_alive(pid: Any): Any`

Check if an FSM process is still alive.

**Returns**: Boolean-like value indicating if the FSM is running

**Example:**
```cure
let alive = fsm_is_alive(fsm_pid)
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

## Complete Example: Traffic Light

Here's a complete working example from `examples/06_fsm_traffic_light.cure`:

```cure
module TrafficLightFSM do
  export [main/0]
  
  import Std.Fsm [fsm_spawn/2, fsm_cast/2, fsm_advertise/2, fsm_state/1]
  import Std.Io [println/1]
  import Std.Pair [pair/2]
  
  # Payload record - tracks traffic light statistics
  record TrafficPayload do
    cycles_completed: Int
    timer_events: Int
    emergency_stops: Int
  end
  
  # Define the TrafficLight FSM
  # Initial state is Red (first state in transitions)
  fsm TrafficPayload{cycles_completed: 0, timer_events: 0, emergency_stops: 0} do
    Red --> |timer| Green
    Red --> |emergency| Red
    Green --> |timer| Yellow
    Green --> |emergency| Red
    Yellow --> |timer| Red
    Yellow --> |emergency| Red
  end
  
  # Main demonstration
  def main(): Int =
    # Initialize FSM with starting data
    let initial_data = TrafficPayload{cycles_completed: 0, timer_events: 0, emergency_stops: 0}
    let fsm_pid = fsm_spawn(:TrafficPayload, initial_data)
    
    # Give the FSM a friendly name
    let adv_result = fsm_advertise(fsm_pid, :traffic_light)
    
    # Check initial state (should be Red)
    let state0 = fsm_state(:traffic_light)
    
    # Send timer event: Red -> Green
    let event1 = pair(:timer, [])
    let cast1 = fsm_cast(:traffic_light, event1)
    let state1 = fsm_state(:traffic_light)  # Now Green
    
    # Send timer event: Green -> Yellow
    let event2 = pair(:timer, [])
    let cast2 = fsm_cast(:traffic_light, event2)
    let state2 = fsm_state(:traffic_light)  # Now Yellow
    
    # Send emergency event: Yellow -> Red
    let event3 = pair(:emergency, [])
    let cast3 = fsm_cast(:traffic_light, event3)
    let state3 = fsm_state(:traffic_light)  # Back to Red
    
    0
end
```

**This example demonstrates:**
- Defining a payload record with fields
- Creating an FSM with initial payload values
- Spawning the FSM with `fsm_spawn/2`
- Naming the FSM with `fsm_advertise/2`
- Sending events using `pair/2` and `fsm_cast/2`
- Querying state with `fsm_state/1`
- Self-transitions (emergency event from Red stays in Red)

## Future Enhancements

Potential additions to the FSM API:
- `fsm_call/2`: Synchronous event sending with reply
- Timeout support: `State --> |timeout(1000)| NextState`
- State entry/exit actions with explicit handler functions
- Guards on transitions: `State --> |event| when condition State2`
- FSM supervision trees integration
- FSM serialization/deserialization for persistence
- Pattern matching on event data in transitions
