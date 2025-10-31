# Cure FSM Usage Guide

**Last Updated**: October 31, 2025

This document provides comprehensive guidance on using Finite State Machines (FSMs) in the Cure programming language.

## Introduction

Cure provides first-class support for Finite State Machines (FSMs) as a core language feature. FSMs in Cure compile directly to BEAM `gen_statem` processes and provide:

- **Declarative Syntax**: Simple arrow-based transition definitions
- **Type-safe**: FSM definitions are checked at compile time  
- **Record-based Payloads**: Structured data carried through transitions
- **Process-based**: Each FSM instance runs as a separate BEAM process
- **Named References**: FSMs can be registered with atoms for easy access

## Quick Start

Here's a minimal FSM example:

```cure
module SimpleFSM do
  export [main/0]
  
  import Std.Fsm [fsm_spawn/2, fsm_cast/2, fsm_advertise/2, fsm_state/1]
  import Std.Pair [pair/2]
  
  # Define payload record
  record SimplePayload do
    counter: Int
  end
  
  # Define FSM with transitions
  fsm SimplePayload{counter: 0} do
    Idle --> |start| Running
    Running --> |stop| Idle
  end
  
  def main(): Int =
    # Spawn FSM
    let initial_data = SimplePayload{counter: 0}
    let fsm_pid = fsm_spawn(:SimplePayload, initial_data)
    
    # Name it
    let _ = fsm_advertise(fsm_pid, :simple_fsm)
    
    # Send event
    let event = pair(:start, [])
    let _ = fsm_cast(:simple_fsm, event)
    
    # Query state
    let current_state = fsm_state(:simple_fsm)  # Returns :Running
    
    0
end
```

## Defining FSMs in Cure

### Basic Structure

Every FSM definition requires:
1. A payload record
2. An `fsm` block with initial payload values
3. Transition definitions using arrow syntax

```cure
# 1. Define payload record
record MyPayload do
  field1: Type1
  field2: Type2
end

# 2. Define FSM
fsm MyPayload{field1: value1, field2: value2} do
  StateA --> |event1| StateB
  StateB --> |event2| StateC
  StateC --> |event3| StateA
end
```

### Transition Syntax

Transitions use the format: `FromState --> |event| ToState`

- **States**: Capitalized identifiers (become atoms at runtime)
- **Events**: Lowercase identifiers in `|event|` notation
- **Initial State**: The first state mentioned is the initial state

**Example:**
```cure
fsm TrafficPayload{cycles: 0} do
  Red --> |timer| Green      # Red is initial state
  Green --> |timer| Yellow
  Yellow --> |timer| Red
end
```

### Self-Transitions

A state can transition to itself:

```cure
fsm DoorPayload{locked: true} do
  Locked --> |unlock| Unlocked
  Locked --> |knock| Locked    # Self-transition
  Unlocked --> |lock| Locked
end
```

## Working with Payloads

Payloads are records that carry data through FSM transitions. They must be defined before the FSM.

### Payload Record Definition

```cure
record TrafficPayload do
  cycles_completed: Int
  timer_events: Int
  emergency_stops: Int
end
```

### Initializing Payload

Provide initial values in the FSM declaration:

```cure
fsm TrafficPayload{cycles_completed: 0, timer_events: 0, emergency_stops: 0} do
  # transitions...
end
```

### Payload Purpose

Payloads are useful for:
- Tracking statistics (counters, timestamps)
- Storing configuration
- Maintaining state-specific data
- Debugging information

## Using FSMs from Cure Code

### Required Imports

```cure
import Std.Fsm [fsm_spawn/2, fsm_cast/2, fsm_advertise/2, fsm_state/1]
import Std.Pair [pair/2]
```

### Spawning an FSM

Use `fsm_spawn/2` with the payload type and initial data:

```cure
let initial_data = TrafficPayload{cycles_completed: 0, timer_events: 0, emergency_stops: 0}
let fsm_pid = fsm_spawn(:TrafficPayload, initial_data)
```

### Registering a Name

Make the FSM accessible by name:

```cure
let _ = fsm_advertise(fsm_pid, :traffic_light)
# Now you can use :traffic_light instead of fsm_pid
```

### Sending Events

Events are sent using pairs (tuples):

```cure
# Create event with empty data list
let empty_list = []
let event = pair(:timer, empty_list)

# Send to FSM
let _ = fsm_cast(:traffic_light, event)
```

### Querying State

Get the current state:

```cure
let current_state = fsm_state(:traffic_light)
# Returns atom like :Red, :Green, or :Yellow
```

## Complete Working Example

Here's the traffic light example from `examples/06_fsm_traffic_light.cure`:

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
  # Events: :timer (normal progression), :emergency (immediate red)
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
    println("=== Traffic Light FSM Demo ===")
    println("")
    
    # Initialize FSM with starting data
    let initial_data = TrafficPayload{cycles_completed: 0, timer_events: 0, emergency_stops: 0}
    let fsm_pid = fsm_spawn(:TrafficPayload, initial_data)
    
    # Give the FSM a friendly name
    let adv_result = fsm_advertise(fsm_pid, :traffic_light)
    
    # Check initial state (should be Red - first in transition list)
    println("Initial state:")
    let state0 = fsm_state(:traffic_light)
    println("State: Red (expected)")
    println("")
    
    # Scenario 1: Normal timer progression Red -> Green
    println("Scenario 1: Timer event from Red")
    let empty1 = []
    let event1 = pair(:timer, empty1)
    let cast1 = fsm_cast(:traffic_light, event1)
    let state1 = fsm_state(:traffic_light)
    println("State: Green (expected)")
    println("")
    
    # Scenario 2: Normal timer progression Green -> Yellow
    println("Scenario 2: Timer event from Green")
    let empty2 = []
    let event2 = pair(:timer, empty2)
    let cast2 = fsm_cast(:traffic_light, event2)
    let state2 = fsm_state(:traffic_light)
    println("State: Yellow (expected)")
    println("")
    
    # Scenario 3: Emergency from Yellow -> Red
    println("Scenario 3: Emergency stop from Yellow")
    let empty3 = []
    let event3 = pair(:emergency, empty3)
    let cast3 = fsm_cast(:traffic_light, event3)
    let state3 = fsm_state(:traffic_light)
    println("State: Red (expected - emergency stop)")
    println("")
    
    println("=== Demo Complete ===")
    0
end
```

## API Reference

### Core Functions

#### `fsm_spawn(fsm_type: Atom, initial_data: Any): Pid`
Spawn a new FSM instance.
- `fsm_type`: Payload record type name (e.g., `:TrafficPayload`)
- `initial_data`: Initial payload record instance
- Returns: Process ID

#### `fsm_cast(target: Pid | Atom, event: Pair): Any`
Send an event to an FSM (asynchronous).
- `target`: FSM Pid or registered name
- `event`: Pair of `(event_name, event_data)` created with `pair/2`
- Returns: Cast result

#### `fsm_advertise(pid: Pid, name: Atom): Any`
Register a name for an FSM process.
- `pid`: FSM process ID
- `name`: Atom to register (e.g., `:my_fsm`)
- Returns: Advertisement result

#### `fsm_state(target: Pid | Atom): Atom`
Query current FSM state.
- `target`: FSM Pid or registered name
- Returns: Current state atom

### Additional Functions

#### `fsm_stop(pid: Pid): Any`
Stop an FSM instance gracefully.

#### `fsm_info(pid: Pid): Any`
Get detailed FSM information (state, data, history).

#### `fsm_is_alive(pid: Pid): Bool`
Check if FSM process is running.

## Best Practices

1. **Keep States Simple**: Each state should represent a clear mode of operation
2. **Use Descriptive Names**: State and event names should be self-documenting
3. **Initialize Payloads**: Always provide initial values for all record fields
4. **Name Your FSMs**: Use `fsm_advertise/2` for important FSMs
5. **Handle All Transitions**: Ensure every state can handle expected events
6. **Use Self-Transitions**: For events that don't change state but need to be acknowledged
7. **Track Statistics**: Use payload fields to track FSM behavior (counters, timestamps)

## Troubleshooting

### FSM Not Responding
- Verify FSM process is alive with `fsm_is_alive/1`
- Check that you're using the correct registered name or Pid
- Ensure events are created correctly with `pair/2`

### Wrong Initial State
- Remember: the first state in the transition list is the initial state
- Check the order of your transitions in the `fsm` block

### Event Not Causing Transition
- Verify the event name matches exactly (case-sensitive)
- Check that a transition exists for that event from the current state
- Use `fsm_state/1` to confirm the current state before sending events

### Import Errors
- Make sure to import `Std.Fsm` functions
- Don't forget to import `Std.Pair [pair/2]` for creating events
- Import `Std.Io [println/1]` if you need to print output

## See Also

- [FSM_API_DESIGN.md](FSM_API_DESIGN.md) - Detailed API design documentation
- [FSM_IMPLEMENTATION_SUMMARY.md](FSM_IMPLEMENTATION_SUMMARY.md) - Implementation details
- [examples/06_fsm_traffic_light.cure](../examples/06_fsm_traffic_light.cure) - Complete working example
- [lib/std/fsm.cure](../lib/std/fsm.cure) - Standard library FSM module

---

For questions or issues, consult the main Cure documentation or examine the FSM runtime source code in `src/fsm/`.
