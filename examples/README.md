# Cure Language Examples

This directory contains working examples demonstrating various features of the Cure programming language. All examples have been compiled and tested successfully.

## Quick Start

Run any example:
```bash
# Examples 1-5: Standard execution
./cure examples/01_list_basics.cure
erl -pa _build/ebin -pa lib/_build -noshell -s ListBasics main -s init stop

# Example 6: FSM (requires special setup)
./examples/run_06_fsm.sh
```

## Examples Overview

### 01_list_basics.cure
**Demonstrates**: Fundamental list operations
- List literals
- `map` - transforming list elements
- `filter` - selecting elements by predicate
- `fold` - reducing lists to single values
- Lambda functions with lists

**Run**:
```bash
./cure examples/01_list_basics.cure
erl -pa _build/ebin -pa lib/_build -noshell -s ListBasics main -s init stop
```

### 02_result_handling.cure
**Demonstrates**: Error handling with Result type
- Result type for safe error handling
- `ok` and `error` constructors
- Pattern matching on Result values
- `and_then` for chaining operations
- Custom error messages

**Run**:
```bash
./cure examples/02_result_handling.cure
erl -pa _build/ebin -pa lib/_build -noshell -s ResultHandling main -s init stop
```

### 03_option_type.cure
**Demonstrates**: Custom option-like types
- Defining custom sum types
- Type constructors (Found/NotFound)
- Pattern matching on custom types
- Safe list access with custom types
- Wildcard patterns in match expressions

**Run**:
```bash
./cure examples/03_option_type.cure
erl -pa _build/ebin -pa lib/_build -noshell -s OptionType main -s init stop
```

### 04_strings.cure
**Demonstrates**: String literals and handling
- String type basics
- String literals
- Functions returning strings
- Direct string output with `println`
- UTF-8 string support

**Run**:
```bash
./cure examples/04_strings.cure
erl -pa _build/ebin -pa lib/_build -noshell -s Strings main -s init stop
```

### 05_recursion.cure
**Demonstrates**: Recursive functions
- Factorial computation
- Fibonacci sequence
- Recursive list sum
- Recursive list counting
- Base cases and recursive cases

**Run**:
```bash
./cure examples/05_recursion.cure
erl -pa _build/ebin -pa lib/_build -noshell -s Recursion main -s init stop
```

### 06_fsm_traffic_light.cure
**Demonstrates**: Finite State Machine (FSM) with full runtime support ✅
- FSM definition with `fsm` keyword
- Record-based payload tracking
- State transitions with events
- Multiple states (Red, Green, Yellow)
- Event handling (timer, emergency)
- FSM API imports (spawn, cast, advertise, state query)
- Complete FSM lifecycle from spawn to state transitions

**Run**:
```bash
# Using the provided run script (recommended):
./examples/run_06_fsm.sh

# Or manually:
./cure examples/06_fsm_traffic_light.cure
erl -pa _build/ebin -pa _build/lib -noshell -eval "
code:load_file('TrafficLightFSM'),
'TrafficLightFSM':register_fsms(),
timer:sleep(50),
'TrafficLightFSM':main()."
```

**Important**: FSM examples require calling `register_fsms()` before `main()` to properly register the FSM definitions with the runtime.

This example demonstrates:
- Proper FSM declaration syntax with records
- Transition rules using `-->` and `|event|` notation
- State progression through timer events (Red → Green → Yellow → Red)
- Emergency transitions from any state to Red
- Self-transitions (emergency while already Red)
- FSM state queries and event casting

For FSM implementation details, see `docs/FSM_*.md` files.

## Common Patterns

### Module Structure
All examples follow this structure:
```cure
module ModuleName do
  export [main/0]
  
  import Std.Module [function/arity]
  
  # Function definitions
  
  def main(): Int =
    # Main logic
    0
end
```

### Pattern Matching
Pattern matching is used extensively:
```cure
match value do
  pattern1 -> result1
  pattern2 -> result2
  _ -> default
end
```

### Let Bindings
Local bindings use `let`:
```cure
let variable = expression
```

### Lambda Functions
Anonymous functions use `fn ... end`:
```cure
fn(x) -> x * 2 end
fn(x, y) -> x + y end
```

### FSM Syntax
Finite State Machines use records and transitions:
```cure
record PayloadName do
  field: Type
end

fsm PayloadName{field: value} do
  State1 --> |event| State2
  State2 --> |event| State1
end
```

## Notes

- All examples (1-6) compile and run successfully ✅
- Optimization warnings can be safely ignored
- Examples use only features from the standard library
- Pattern matching requires all cases to be handled or a wildcard `_`
- Match expressions cannot have variables that escape their scope
- Use `match` for control flow, not if-then-else
- Records are supported for FSM payload definitions
- FSM examples require `register_fsms()` to be called before `main()`

## Building All Examples

To compile all examples at once:
```bash
for file in examples/*.cure; do
  echo "Compiling $file..."
  ./cure "$file"
done
```

## Next Steps

For more advanced examples, see:
- `examples.second_phase/turnstile.cure` - FSM example
- `lib/std/` - Standard library implementations
- `docs/` - Language documentation
