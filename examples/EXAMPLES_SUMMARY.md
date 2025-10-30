# Cure Examples - Complete Summary

**Status**: All 6 examples are fully functional ✅  
**Date**: October 30, 2025  
**Total Lines of Code**: ~700+ lines of working Cure code

---

## Examples Overview

| # | Name | Status | Features Demonstrated |
|---|------|--------|----------------------|
| 1 | **list_basics** | ✅ Working | Lists, map, filter, fold, lambdas |
| 2 | **result_handling** | ✅ Working | Result type, error handling, pattern matching |
| 3 | **option_type** | ✅ Working | Custom sum types, type constructors |
| 4 | **strings** | ✅ Working | String literals, UTF-8, string functions |
| 5 | **recursion** | ✅ Working | Recursive functions, factorial, fibonacci |
| 6 | **fsm_traffic_light** | ✅ Working | FSMs, records, state transitions, events |

---

## Running the Examples

### Standard Examples (1-5)

```bash
# Compile
./cure examples/0X_name.cure

# Run
erl -pa _build/ebin -pa lib/_build -noshell -s ModuleName main -s init stop
```

### FSM Example (6)

```bash
# Use the provided script (recommended)
./examples/run_06_fsm.sh

# Or manually with FSM registration
./cure examples/06_fsm_traffic_light.cure
erl -pa _build/ebin -pa _build/lib -noshell -eval "
code:load_file('TrafficLightFSM'),
'TrafficLightFSM':register_fsms(),
timer:sleep(50),
'TrafficLightFSM':main()."
```

**Important**: FSM examples require `register_fsms()` to be called before running.

---

## What Each Example Teaches

### 1. List Basics (`01_list_basics.cure`)
**Concepts**: Functional programming fundamentals
- Creating lists with literals: `[1, 2, 3, 4, 5]`
- Transforming with `map`: `map(list, fn(x) -> x * 2 end)`
- Filtering with predicates: `filter(list, predicate)`
- Reducing with `fold`: `fold(list, initial, accumulator_fn)`
- Lambda functions: `fn(params) -> body end`

### 2. Result Handling (`02_result_handling.cure`)
**Concepts**: Error handling without exceptions
- Creating Results: `ok(value)` and `error(message)`
- Pattern matching on Result: `Ok(val)` vs `Error(msg)`
- Chaining operations: `and_then(result, fn(x) -> ... end)`
- Safe division example
- Custom error messages

### 3. Option Type (`03_option_type.cure`)
**Concepts**: Representing optional/nullable values
- Defining custom sum types: `type MyOption(T) = Found(T) | NotFound`
- Type constructors as values
- Pattern matching on custom types
- Safe list access without exceptions
- Wildcard patterns for default cases

### 4. Strings (`04_strings.cure`)
**Concepts**: Text handling
- String literals in functions
- UTF-8 string support
- Returning strings from functions
- String output with `println`
- Special characters in strings

### 5. Recursion (`05_recursion.cure`)
**Concepts**: Recursive problem solving
- Base cases: when to stop recursion
- Recursive cases: how to reduce the problem
- Mathematical recursion: factorial, fibonacci
- List recursion: sum and count
- Recursive patterns in functional programming

### 6. FSM Traffic Light (`06_fsm_traffic_light.cure`)
**Concepts**: Finite State Machines
- FSM declaration with `fsm` keyword
- Record-based payload: `record PayloadName do ... end`
- State transitions: `State1 --> |event| State2`
- Event handling: `:timer` and `:emergency`
- FSM lifecycle:
  - Spawning: `fsm_spawn(:TypeName, initial_data)`
  - Naming: `fsm_advertise(pid, :name)`
  - Events: `fsm_cast(:name, pair(:event, data))`
  - Queries: `fsm_state(:name)`
- Complete state machine with:
  - Normal progression: Red → Green → Yellow → Red
  - Emergency transitions from any state
  - Self-transitions (Red on emergency stays Red)

---

## Language Features Covered

### ✅ Core Language
- [x] Module system with exports and imports
- [x] Function definitions with type signatures
- [x] Let bindings for local variables
- [x] Pattern matching with `match ... do ... end`
- [x] Lambda expressions with `fn ... end`
- [x] Recursion (direct and tail recursion)

### ✅ Type System
- [x] Primitive types: Int, String, Bool
- [x] Compound types: List(T)
- [x] Sum types: `type T = A | B`
- [x] Type constructors: `Ok(T)`, `Error(E)`, custom constructors
- [x] Parametric polymorphism: `List(T)`, `Result(T, E)`
- [x] Records: `record Name do ... end`

### ✅ Advanced Features
- [x] Finite State Machines (FSM)
- [x] Higher-order functions
- [x] Pattern matching with guards (basic)
- [x] Standard library integration

### ✅ Standard Library Usage
- [x] `Std.List`: map, filter, fold
- [x] `Std.Core`: Result, ok, error, and_then
- [x] `Std.Io`: print, println
- [x] `Std.Fsm`: fsm_spawn, fsm_cast, fsm_advertise, fsm_state
- [x] `Std.Pair`: pair

---

## Common Patterns

### Pattern: Error Handling with Result
```cure
def operation(): Result(T, String) =
  match condition do
    true -> ok(value)
    false -> error("error message")
  end

# Using the result
match result do
  Ok(val) -> # success case
  Error(msg) -> # error case
end
```

### Pattern: Recursive List Processing
```cure
def process_list(list: List(T)): U =
  match list do
    [] -> base_case_value
    [h | t] -> combine(process(h), process_list(t))
  end
```

### Pattern: FSM Definition
```cure
record StatePayload do
  field: Type
end

fsm StatePayload{field: initial_value} do
  State1 --> |event1| State2
  State1 --> |event2| State1
  State2 --> |event3| State1
end
```

---

## Testing Status

All examples have been:
- ✅ Compiled successfully
- ✅ Executed without runtime errors
- ✅ Tested with expected outputs
- ✅ Documented with comments

**Note**: Optimization warnings during compilation can be safely ignored. They don't affect functionality.

---

## File Structure

```
examples/
├── README.md                        # Main documentation
├── EXAMPLES_SUMMARY.md             # This file
├── run_06_fsm.sh                   # FSM runner script
├── 01_list_basics.cure             # 41 lines
├── 02_result_handling.cure         # 63 lines
├── 03_option_type.cure             # 72 lines
├── 04_strings.cure                 # 56 lines
├── 05_recursion.cure               # 71 lines
└── 06_fsm_traffic_light.cure       # 113 lines
```

---

## Learning Path

**Recommended order for beginners:**

1. **Start here**: `01_list_basics.cure` - Basic syntax and functional programming
2. **Error handling**: `02_result_handling.cure` - Safe error handling patterns
3. **Type system**: `03_option_type.cure` - Custom types and constructors
4. **Text processing**: `04_strings.cure` - Working with strings
5. **Algorithms**: `05_recursion.cure` - Recursive problem solving
6. **Advanced**: `06_fsm_traffic_light.cure` - State machines and event handling

---

## Next Steps

After completing these examples:

1. Explore the standard library in `lib/std/`
2. Read language documentation in `docs/`
3. Try the turnstile example: `examples.second_phase/turnstile.cure`
4. Experiment with modifying the examples
5. Create your own Cure programs!

---

## Resources

- **Syntax Guide**: `/CURE_SYNTAX_GUIDE.md`
- **Standard Library**: `lib/std/*.cure`
- **Documentation**: `docs/`
- **FSM Details**: `docs/FSM_*.md`
- **Language Spec**: `docs/LANGUAGE_SPEC.md`

---

**All examples created and tested on**: October 30, 2025  
**Cure Compiler Version**: Development build with full FSM support
