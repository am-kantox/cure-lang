# Guard Compilation in Cure

The Cure programming language implements a comprehensive guard compilation system that transforms guard expressions into efficient BEAM bytecode instructions. Guards are expressions that can be evaluated safely in restricted contexts like pattern matching, FSM transitions, and function parameter constraints.

## Overview

Guards in Cure provide:
- **Safety**: Only side-effect-free expressions allowed
- **Performance**: Compiled to optimized BEAM instructions
- **Integration**: Works seamlessly with FSMs, pattern matching, and function definitions
- **Optimization**: Constant folding, dead code elimination, and boolean simplification

## Guard Contexts

Guards can appear in several contexts within Cure programs:

### 1. Pattern Matching Guards

```cure
match value do
  x when x > 10 -> "large"
  x when x > 0 -> "positive"
  _ -> "other"
end
```

### 2. FSM Transition Guards

```cure
fsm Counter do
  states: [Zero, Positive, Negative]
  initial: Zero
  
  state Zero do
    event(:increment) -> Positive
    event(:decrement) -> Negative
  end
  
  state Positive do
    event(:decrement) when count > 1 -> Positive
    event(:decrement) when count == 1 -> Zero
    event(:reset) -> Zero
  end
end
```

### 3. Function Parameter Constraints

```cure
def divide(a: Int, b: Int) when b != 0: Float =
  a / b
```

## Supported Guard Expressions

### Comparison Operators
- `==`, `!=` - Value equality/inequality
- `=:=`, `=/=` - Strict equality/inequality  
- `<`, `>`, `<=`, `>=` - Numeric comparisons

### Arithmetic Operators
- `+`, `-`, `*`, `/` - Basic arithmetic
- `div`, `rem` - Integer division and remainder
- `abs`, `trunc`, `round` - Numeric functions

### Boolean Operators
- `and`, `or`, `not` - Boolean logic
- `andalso`, `orelse` - Short-circuit boolean operators
- `xor` - Exclusive or

### Bitwise Operators
- `band`, `bor`, `bxor`, `bnot` - Bitwise operations
- `bsl`, `bsr` - Bit shifts

### Type Guards
- `is_atom`, `is_binary`, `is_boolean`
- `is_float`, `is_integer`, `is_number`
- `is_list`, `is_tuple`, `is_pid`
- `is_function`, `is_reference`, `is_port`

### List/Tuple Operations
- `length` - List length
- `size` - Tuple/binary size
- `hd`, `tl` - List head/tail
- `element` - Tuple element access

## Compilation Process

The guard compilation process consists of several phases:

### 1. Safety Analysis

```erlang
cure_guard_compiler:is_guard_safe(Guard)
```

Validates that the guard expression only uses allowed operations and functions. Unsafe expressions (like arbitrary function calls) are rejected.

### 2. Optimization

```erlang
cure_guard_compiler:optimize_guard(Guard)
```

Applies several optimization techniques:

**Constant Folding**: Evaluates constant expressions at compile time
```cure
# Before optimization
x > 5 + 3

# After optimization  
x > 8
```

**Boolean Simplification**: Simplifies boolean logic
```cure
# Before optimization
true andalso condition

# After optimization
condition
```

### 3. Code Generation

```erlang
cure_guard_compiler:compile_guard(Guard, State)
```

Generates BEAM instruction sequences:

```erlang
% Example: x > 10 becomes:
[
  #beam_instr{op = load_param, args = [x]},
  #beam_instr{op = load_literal, args = [10]}, 
  #beam_instr{op = guard_bif, args = ['>', 2]}
]
```

## Implementation Architecture

### Core Modules

**`cure_guard_compiler.erl`**
- Main compilation interface
- Safety analysis and optimization
- BEAM instruction generation

**`cure_codegen.erl`**
- Integration with pattern matching
- Function constraint compilation
- Match clause handling

**`cure_fsm_runtime.erl`**
- FSM guard evaluation
- Compiled instruction execution
- Runtime guard checking

### Data Structures

**Guard Instructions**
```erlang
#beam_instr{
  op = guard_bif,      % Instruction type
  args = ['>', 2],     % Operator and arity
  location = Location  % Source location
}
```

**Compilation Context**
```erlang
#{
  state => FSMState,
  event_data => EventData,
  variables => Variables,
  stack => InstructionStack
}
```

## Examples

### Basic Guard Compilation

```cure
# Source code
def process(x: Int) when x > 0 =
  x * 2
```

```erlang
% Generated instructions
[
  #beam_instr{op = load_param, args = [x]},
  #beam_instr{op = load_literal, args = [0]},
  #beam_instr{op = guard_bif, args = ['>', 2]},
  #beam_instr{op = guard_check, args = [function_clause_error]}
]
```

### Complex Guard Expression

```cure
# Source code  
match value do
  {x, y} when x > 5 and y < 10 -> "valid"
  _ -> "invalid" 
end
```

```erlang
% Generated instructions for guard
[
  #beam_instr{op = load_param, args = [x]},
  #beam_instr{op = load_literal, args = [5]},
  #beam_instr{op = guard_bif, args = ['>', 2]},
  #beam_instr{op = load_param, args = [y]},
  #beam_instr{op = load_literal, args = [10]},
  #beam_instr{op = guard_bif, args = ['<', 2]},
  #beam_instr{op = guard_bif, args = ['and', 2]}
]
```

### FSM Guard Integration

```cure
fsm SmartCounter do
  state Positive do
    event(:decrement) when count > 1 -> Positive
    event(:decrement) when count == 1 -> Zero
  end
end
```

The FSM runtime executes compiled guards using a virtual machine that evaluates instruction sequences against the current FSM state and event data.

## Performance Characteristics

### Optimization Benefits
- **Constant folding**: Eliminates runtime computation for constant expressions
- **Dead code elimination**: Removes unreachable guard branches
- **Instruction combining**: Merges adjacent operations where possible

### Runtime Performance
- Guards compile to efficient BEAM instructions
- Type guards map directly to BEAM's built-in type tests
- Comparison operations use BEAM's optimized comparison instructions
- Short-circuit evaluation for boolean operators

## Error Handling

### Compile-Time Errors
- **Unsafe guard expressions**: Using non-guard-safe functions
- **Invalid operators**: Using unsupported operators in guards
- **Type mismatches**: When guard expressions don't match expected types

### Runtime Errors
- **Guard failures**: When guard evaluation throws an exception
- **Pattern match failures**: When guards fail during pattern matching
- **Function clause errors**: When function guards don't match

## Testing

The guard compilation system includes comprehensive tests covering:
- Safety analysis for various expression types
- Compilation of different guard operators
- Optimization correctness
- FSM integration
- Error handling scenarios

Run tests with:
```bash
erl -pa _build/ebin -s guard_compilation_test run -s init stop
```

## Integration with Type System

Guards work closely with Cure's type system:
- Guard expressions must be well-typed
- Type guards provide runtime type validation
- Dependent types can use guards for constraint validation
- Pattern matching integrates guard results with type inference

## Future Enhancements

Planned improvements include:
- Advanced pattern compilation with guard integration
- Profile-guided guard optimization
- Custom guard function definitions
- Integration with dependent type constraints
- JIT compilation of frequently-used guards

## Best Practices

1. **Keep guards simple**: Complex logic should be moved to functions
2. **Use type guards**: Prefer `is_integer(x)` over complex type checks
3. **Optimize for common cases**: Put most likely guards first
4. **Avoid side effects**: Guards must be pure expressions
5. **Test guard coverage**: Ensure all guard branches are tested

This guard compilation system provides a robust foundation for safe, efficient conditional logic in Cure programs, supporting the language's goals of type safety and performance.