# Action Compilation System

This document describes the action compilation system in the Cure programming language, which provides compile-time compilation of action expressions for FSM transitions with optimized runtime execution.

## Overview

The action compilation system extends FSM capabilities by allowing complex actions to be executed when state transitions occur. Actions are compiled from AST expressions into BEAM bytecode instructions for efficient execution in the FSM runtime.

## Architecture

### Components

1. **Action Compiler** (`cure_action_compiler.erl`): Compiles action expressions to BEAM instructions
2. **Parser Extensions** (`cure_parser.erl`): Parses action syntax in FSM transitions 
3. **FSM Runtime Integration** (`cure_fsm_runtime.erl`): Executes compiled actions during transitions
4. **Codegen Integration** (`cure_codegen.erl`): Integrates actions into FSM compilation

### Compilation Pipeline

```
Action AST → Safety Analysis → Optimization → BEAM Instructions → Runtime Execution
```

## Action Types

### State Modification Actions

#### Variable Assignment
```cure
do counter = 42
```
Compiled to instructions that update FSM state variables.

#### Field Update
```cure
do state.speed = 100
```
Updates specific fields in structured state data.

#### Increment/Decrement
```cure
do counter += 5
do counter -= 3
```
Optimized arithmetic operations on state variables.

### Communication Actions

#### Event Emission
```cure
do emit(next_event)
do emit(data_event, #{value: 123})
```
Sends events to the FSM or other processes.

#### Logging
```cure
do log(info, "State transition completed")
```
Structured logging with different severity levels.

### Computational Actions

#### Function Calls
```cure
do result = length(state.items)
do items = lists_reverse(state.queue)
```
Calls to safe, pure functions approved for FSM context.

#### Binary Operations
```cure
do result = x + y * 2
do message = prefix ++ suffix
```
Mathematical and list operations on state values.

### Control Flow Actions

#### Conditional Actions
```cure
do if counter > 10 then
    counter = 0
else
    counter += 1
end
```
Conditional execution based on state or event data.

#### Action Sequences
```cure
do {
    counter = 0;
    log(info, "Counter reset");
    emit(counter_reset)
}
```
Multiple actions executed in sequence.

## Safety Analysis

The action compiler performs comprehensive safety analysis to ensure actions:

- Only access allowed state variables and fields
- Use approved functions and operations
- Cannot perform unsafe operations (spawn, file I/O, network, etc.)
- Maintain FSM determinism and predictability

### Safe Operations

- State variable and field access/modification
- Event data access
- Current state inspection
- Mathematical operations (+, -, *, /, div, rem)
- List operations (++, --, length, reverse)
- Map operations (get, put)
- Pure function calls (abs, max, min, round, etc.)

### Unsafe Operations (Rejected)

- Process spawning or messaging
- File system operations
- Network operations
- System calls
- Unsafe function calls

## Optimization Passes

### Constant Folding
```cure
# Before optimization
do result = 5 + 3 * 2

# After optimization  
do result = 11
```

### Dead Code Elimination
```cure
# Before optimization
do counter += 0

# After optimization
# (removed - no-op)
```

### Sequence Simplification
```cure
# Before optimization
do { single_action }

# After optimization
do single_action
```

## Syntax Reference

### Basic Syntax
Actions are specified in FSM transitions using the `do` keyword:

```cure
state idle do
    event(start) -> active do
        counter = 1
    end
end
```

### Complex Actions
```cure
state processing do
    event(data) -> ready do {
        items = event_data.items;
        count = length(items);
        if count > 0 then
            log(info, "Processing items")
        else
            log(warning, "No items to process")
        end;
        emit(ready, #{count: count})
    }
    end
end
```

## Value Access

### State Variables
```cure
do temp = counter        # Read state variable
do counter = temp + 1    # Write state variable
```

### State Fields
```cure
do speed = state.velocity    # Read state field
do state.position = new_pos  # Write state field
```

### Event Data
```cure
do data = event_data         # Access event data
do name = event_data.name    # Access event data field
```

### Current State
```cure
do prev_state = current_state
```

## Compilation Process

### 1. Parsing
The parser recognizes action syntax and creates AST nodes:

```erlang
#transition{
    event = start_event,
    target = active,
    action = {assign, counter, {literal, 1, Location}, Location}
}
```

### 2. Safety Analysis
Actions are analyzed for safety before compilation:

```erlang
case cure_action_compiler:analyze_action_safety(Action, #{}) of
    {ok, safe, Details} -> proceed_compilation();
    {ok, unsafe, Reasons} -> {error, {unsafe_action, Reasons}}
end
```

### 3. Optimization
Safe actions are optimized using multiple passes:

```erlang
OptimizedAction = cure_action_compiler:optimize_action(Action)
```

### 4. Instruction Generation
Optimized actions are compiled to BEAM instructions:

```erlang
{ok, Instructions, State} = cure_action_compiler:compile_action(OptimizedAction, State)
```

### 5. Runtime Integration
Compiled actions are integrated into FSM definitions:

```erlang
CompiledTransition = {TargetState, Guard, {compiled_action, Instructions}}
```

## Runtime Execution

### Execution Context
Actions execute in a controlled FSM context with access to:

- Current FSM state and data
- Event data from the triggering event
- Safe function library
- Logging facilities

### Virtual Machine
The action execution uses a stack-based virtual machine:

```erlang
execute_action_instructions(Instructions, State, EventData) ->
    Context = #{
        state => State,
        event_data => EventData,
        variables => #{},
        stack => []
    },
    Result = execute_instructions(Instructions, Context),
    extract_result(Result).
```

### State Updates
Action execution produces new state data:

```erlang
NewData = cure_fsm_runtime:execute_action({compiled_action, Instructions}, State, EventData)
```

## Error Handling

### Compilation Errors
- **Syntax errors**: Invalid action syntax
- **Safety violations**: Unsafe operations detected
- **Type mismatches**: Incompatible value types

### Runtime Errors  
- **State access errors**: Non-existent variables/fields
- **Arithmetic errors**: Division by zero, overflow
- **Function call errors**: Invalid arguments

All errors are caught and handled gracefully without crashing the FSM.

## Performance Characteristics

### Compilation Time
- Linear in action expression size
- Constant-time safety checks for known operations
- Efficient optimization passes

### Runtime Performance
- Near-native execution speed through BEAM instructions
- Minimal overhead compared to interpreted actions
- Optimized state access and modification

### Memory Usage
- Compiled instructions stored in FSM definition
- Minimal runtime memory allocation
- Stack-based execution model

## Examples

### Complete FSM with Actions

```cure
fsm Counter do
    states: [stopped, running]
    initial: stopped
    
    state stopped do
        event(start) -> running do {
            log(info, "Starting counter");
            count = 0;
            emit(started)
        }
        end
    end
    
    state running do
        event(increment) -> running do {
            count += 1;
            log(debug, "Counter value: " ++ count)
        }
        end
        
        event(reset) -> running do
            if count > 0 then {
                log(info, "Resetting counter from " ++ count);
                count = 0;
                emit(counter_reset)
            } else
                log(warning, "Counter already zero")
            end
        end
        
        event(stop) -> stopped do {
            final_count = count;
            count = 0;
            log(info, "Stopped with final count: " ++ final_count);
            emit(stopped, #{final_count: final_count})
        }
        end
    end
end
```

### Traffic Light with Timing

```cure
fsm TrafficLight do
    states: [red, yellow, green]
    initial: red
    
    state red do
        timeout(30000) -> green do {
            log(info, "Red to Green");
            emit(light_change, #{from: red, to: green})
        }
        end
    end
    
    state green do
        timeout(25000) -> yellow do {
            log(info, "Green to Yellow");
            emit(light_change, #{from: green, to: yellow})
        }
        end
    end
    
    state yellow do
        timeout(5000) -> red do {
            log(info, "Yellow to Red");
            emit(light_change, #{from: yellow, to: red})
        }
        end
    end
end
```

## Best Practices

### Action Design
1. **Keep actions simple**: Complex logic should be in separate functions
2. **Avoid side effects**: Use pure operations where possible
3. **Handle errors gracefully**: Use conditionals to check values
4. **Log important transitions**: Aid debugging and monitoring

### Performance
1. **Use optimizations**: Enable optimization passes in compilation
2. **Minimize state copies**: Update fields rather than replacing entire state
3. **Batch operations**: Use sequences for multiple related actions
4. **Profile FSM behavior**: Monitor performance in production

### Maintainability
1. **Document complex actions**: Explain the purpose and behavior
2. **Use descriptive variable names**: Make code self-documenting
3. **Factor out common patterns**: Create reusable action templates
4. **Test action behavior**: Write comprehensive test cases

## Integration with Other Systems

### Guard Conditions
Actions work together with guard conditions for complex transition logic:

```cure
event(data) when length(event_data.items) > 0 -> processing do {
    items = event_data.items;
    log(info, "Processing " ++ length(items) ++ " items");
    processed_count = 0
}
end
```

### Module System
Actions can call functions from imported modules:

```cure
import Std.Math [abs/1, max/2]

state calculating do
    event(compute) -> done do {
        result = max(abs(x), abs(y));
        emit(result_ready, #{value: result})
    }
    end
end
```

### Type System
Action values integrate with Cure's dependent type system:

```cure
state validated do
    event(input) when is_valid_input(event_data) -> processing do {
        validated_data = validate_and_transform(event_data);
        emit(data_validated, validated_data)
    }
    end
end
```

## Conclusion

The action compilation system provides a powerful, safe, and efficient way to add behavior to FSM state transitions. By combining compile-time safety analysis with runtime optimization, it enables complex FSM behaviors while maintaining the reliability and predictability essential for system programming.

The system successfully balances expressiveness with safety, allowing developers to write sophisticated state machine logic while preventing common errors and security issues through compile-time analysis.