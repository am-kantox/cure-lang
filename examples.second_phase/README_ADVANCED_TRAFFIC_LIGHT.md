# Advanced Traffic Light FSM Example

## Overview

This example demonstrates the Cure programming language's finite state machine (FSM) syntax, translated from the Erlang `advanced_traffic_light_demo.erl` example.

## Features Demonstrated

### FSM Structure
- **4 States**: Red, Green, Yellow, Maintenance
- **Multiple transitions**: Event-driven state changes  
- **Emergency handling**: Transitions to Maintenance from any state
- **Maintenance mode**: Resume capability back to normal operation

### Cure Language Features
- FSM definition syntax (`fsm` keyword)
- State declarations with transition rules
- Event-based transitions (`event(:timer)`, `event(:emergency_stop)`)
- Record types for structured data (`StateData`)
- Module system with exports
- Type annotations

## Compilation

```bash
./cure examples/advanced_traffic_light.cure
```

This produces `_build/ebin/AdvancedTrafficLight.beam`.

## Execution

```bash
erl -pa _build/ebin -pa _build/lib -eval "'AdvancedTrafficLight':main()." -s init stop
```

## FSM Definition

```cure
fsm AdvancedTrafficLight do
  states: [Red, Green, Yellow, Maintenance]
  initial: Red

  state Red do
    event(:timer) -> Green
    event(:emergency_stop) -> Maintenance
  end

  state Green do
    event(:timer) -> Yellow
    event(:emergency_stop) -> Maintenance
  end

  state Yellow do
    event(:timer) -> Red
    event(:emergency_stop) -> Maintenance
  end

  state Maintenance do
    event(:resume) -> Red
  end
end
```

## Comparison with Erlang Version

The Erlang version (`advanced_traffic_light_demo.erl`) includes:
- Runtime FSM execution using `cure_fsm_runtime`
- Action functions with state/payload modifications
- Guard functions for conditional transitions
- Performance monitoring and statistics
- Event history tracking

The Cure version demonstrates the **language syntax** for defining such FSMs. To execute it with the full runtime features, you would integrate with the `cure_fsm_runtime` Erlang module.

## State Data Structure

```cure
record StateData do
  cycles_completed: Int
  total_transitions: Int
  emergency_count: Int
  vehicle_count: Int
end
```

## Note on Print Statements

The current Cure standard library's `print()` function is a stub (returns 0). This example successfully compiles and type-checks, demonstrating the language's FSM capabilities. For actual I/O, the Erlang interop would be used.

## Learning Points

1. **FSM Syntax**: Clean, declarative state machine definitions
2. **Type Safety**: State data is typed via record definitions
3. **Event System**: Explicit event declarations for transitions  
4. **Modularity**: FSMs are first-class language constructs
5. **Composability**: States and transitions are independently defined

## Next Steps

To extend this example:
- Add action functions to modify state data during transitions
- Implement guard conditions for conditional transitions
- Integrate with `cure_fsm_runtime` for execution
- Add timeout-based transitions
- Implement state-specific behaviors

## See Also

- `examples/traffic_light.cure` - Simpler FSM example
- `examples/advanced_traffic_light_demo.erl` - Full Erlang runtime version
- `src/fsm/cure_fsm_runtime.erl` - FSM runtime implementation
