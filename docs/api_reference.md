# Cure API Reference

## Overview

This document provides comprehensive API documentation for all Cure language modules, functions, and built-in operations.

## Table of Contents

1. [Built-in Functions](#built-in-functions)
2. [FSM Functions](#fsm-functions)
3. [Type System Functions](#type-system-functions)
4. [List Operations](#list-operations)
5. [Arithmetic Functions](#arithmetic-functions)
6. [String Functions](#string-functions)
7. [Compiler API](#compiler-api)
8. [Runtime API](#runtime-api)

## Built-in Functions

### Core Language Functions

#### `length/1`
```cure
length(list: List(T)) -> Int
```
Returns the length of a list.

**Example:**
```cure
length([1, 2, 3, 4])  # Returns: 4
length([])            # Returns: 0
```

#### `head/1`
```cure
head(list: List(T, n)) -> T when n > 0
```
Returns the first element of a non-empty list.

**Example:**
```cure
head([1, 2, 3])       # Returns: 1
head(["a", "b"])      # Returns: "a"
```

#### `tail/1`
```cure
tail(list: List(T, n)) -> List(T, n-1) when n > 0
```
Returns a list without its first element.

**Example:**
```cure
tail([1, 2, 3])       # Returns: [2, 3]
tail(["a"])           # Returns: []
```

#### `append/2`
```cure
append(list1: List(T, n), list2: List(T, m)) -> List(T, n+m)
```
Concatenates two lists.

**Example:**
```cure
append([1, 2], [3, 4])     # Returns: [1, 2, 3, 4]
append([], [1, 2])         # Returns: [1, 2]
```

#### `reverse/1`
```cure
reverse(list: List(T, n)) -> List(T, n)
```
Reverses a list.

**Example:**
```cure
reverse([1, 2, 3])    # Returns: [3, 2, 1]
reverse([])           # Returns: []
```

### Type Conversion Functions

#### `int_to_float/1`
```cure
int_to_float(x: Int) -> Float
```
Converts an integer to a float.

**Example:**
```cure
int_to_float(42)      # Returns: 42.0
int_to_float(-10)     # Returns: -10.0
```

#### `float_to_int/1`
```cure
float_to_int(x: Float) -> Int
```
Truncates a float to an integer.

**Example:**
```cure
float_to_int(3.14)    # Returns: 3
float_to_int(-2.9)    # Returns: -2
```

#### `string_to_int/1`
```cure
string_to_int(s: String) -> Result(Int, String)
```
Parses a string as an integer.

**Example:**
```cure
string_to_int("123")  # Returns: Ok(123)
string_to_int("abc")  # Returns: Error("Invalid integer")
```

#### `int_to_string/1`
```cure
int_to_string(x: Int) -> String
```
Converts an integer to its string representation.

**Example:**
```cure
int_to_string(42)     # Returns: "42"
int_to_string(-100)   # Returns: "-100"
```

## FSM Functions

### FSM Lifecycle Functions

#### `fsm_spawn/1`
```cure
fsm_spawn(fsm_type: FSMType) -> FSMPid
```
Creates a new FSM instance of the specified type.

**Example:**
```cure
let light = fsm_spawn(TrafficLight)
```

**Implementation:**
```erlang
fsm_spawn(Type) ->
    cure_fsm_runtime:spawn_fsm(Type).
```

#### `fsm_spawn/2`
```cure
fsm_spawn(fsm_type: FSMType, init_data: T) -> FSMPid
```
Creates a new FSM instance with initialization data.

**Example:**
```cure
let counter = fsm_spawn(Counter, 10)  # Start with initial count of 10
```

**Implementation:**
```erlang
fsm_spawn(Type, InitData) ->
    cure_fsm_runtime:spawn_fsm(Type, InitData).
```

#### `fsm_stop/1`
```cure
fsm_stop(fsm_pid: FSMPid) -> :ok
```
Gracefully stops an FSM instance.

**Example:**
```cure
fsm_stop(light)
```

**Implementation:**
```erlang
fsm_stop(FsmPid) ->
    cure_fsm_runtime:stop_fsm(FsmPid).
```

### FSM Communication Functions

#### `fsm_send/2`
```cure
fsm_send(fsm_pid: FSMPid, event: Event) -> :ok
```
Sends an event to an FSM asynchronously.

**Example:**
```cure
fsm_send(light, :go)
fsm_send(counter, :increment)
fsm_send(door, {:unlock, 1234})
```

**Implementation:**
```erlang
fsm_send(FsmPid, Event) ->
    cure_fsm_runtime:send_event(FsmPid, Event).
```

#### `fsm_send/3`
```cure
fsm_send(fsm_pid: FSMPid, event: Event, timeout: Int) -> :ok | :timeout
```
Sends an event to an FSM with a timeout.

**Example:**
```cure
case fsm_send(server, :request, 5000) do
  :ok -> handle_success()
  :timeout -> handle_timeout()
end
```

**Implementation:**
```erlang
fsm_send(FsmPid, Event, Timeout) ->
    cure_fsm_runtime:send_event_sync(FsmPid, Event, Timeout).
```

### FSM Inspection Functions

#### `fsm_state/1`
```cure
fsm_state(fsm_pid: FSMPid) -> StateName | {StateName, StateData}
```
Returns the current state of an FSM.

**Example:**
```cure
let current = fsm_state(light)       # Returns: Red
let current = fsm_state(counter)     # Returns: {Counting, 5}
```

**Implementation:**
```erlang
fsm_state(FsmPid) ->
    cure_fsm_runtime:get_state(FsmPid).
```

#### `fsm_is_alive/1`
```cure
fsm_is_alive(fsm_pid: FSMPid) -> Bool
```
Checks if an FSM process is still running.

**Example:**
```cure
if fsm_is_alive(light) then
  fsm_send(light, :go)
else
  # Handle dead FSM
end
```

**Implementation:**
```erlang
fsm_is_alive(FsmPid) ->
    is_process_alive(FsmPid).
```

#### `fsm_info/1`
```cure
fsm_info(fsm_pid: FSMPid) -> FSMInfo
```
Returns detailed information about an FSM (for debugging).

**Example:**
```cure
let info = fsm_info(light)
# Returns: {fsm_type: TrafficLight, current_state: Red, ...}
```

**Implementation:**
```erlang
fsm_info(FsmPid) ->
    cure_fsm_runtime:get_fsm_info(FsmPid).
```

## Type System Functions

### Type Checking Functions

#### `type_of/1`
```cure
type_of(value: T) -> Type
```
Returns the type of a value (compile-time function).

**Example:**
```cure
type_of(42)        # Returns: Int
type_of([1, 2])    # Returns: List(Int, 2)
```

#### `is_type/2`
```cure
is_type(value: T, type: Type) -> Bool
```
Checks if a value has a specific type.

**Example:**
```cure
is_type(42, Int)         # Returns: true
is_type("hello", Int)    # Returns: false
```

### Constraint Functions

#### `assert_constraint/1`
```cure
assert_constraint(constraint: Bool) -> Unit
```
Assert that a constraint holds at runtime (for dependent types).

**Example:**
```cure
def safe_divide(x: Float, y: Float) -> Float =
  assert_constraint(y != 0.0)
  x / y
```

## List Operations

### Higher-Order Functions

#### `map/2`
```cure
map(f: (T) -> U, list: List(T, n)) -> List(U, n)
```
Applies a function to each element of a list.

**Example:**
```cure
map(fn(x) -> x * 2 end, [1, 2, 3])  # Returns: [2, 4, 6]
map(string_length, ["hi", "hello"]) # Returns: [2, 5]
```

#### `filter/2`
```cure
filter(predicate: (T) -> Bool, list: List(T, n)) -> List(T, m) when m <= n
```
Filters a list based on a predicate.

**Example:**
```cure
filter(fn(x) -> x > 0 end, [-1, 2, -3, 4])  # Returns: [2, 4]
filter(fn(s) -> length(s) > 3 end, ["hi", "hello", "bye"])  # Returns: ["hello"]
```

#### `fold_left/3`
```cure
fold_left(f: (Acc, T) -> Acc, initial: Acc, list: List(T)) -> Acc
```
Left fold over a list.

**Example:**
```cure
fold_left(fn(acc, x) -> acc + x end, 0, [1, 2, 3, 4])  # Returns: 10
fold_left(fn(acc, x) -> [x | acc] end, [], [1, 2, 3])  # Returns: [3, 2, 1]
```

#### `fold_right/3`
```cure
fold_right(f: (T, Acc) -> Acc, initial: Acc, list: List(T)) -> Acc
```
Right fold over a list.

**Example:**
```cure
fold_right(fn(x, acc) -> x + acc end, 0, [1, 2, 3, 4])  # Returns: 10
fold_right(fn(x, acc) -> [x | acc] end, [], [1, 2, 3])  # Returns: [1, 2, 3]
```

### List Manipulation Functions

#### `take/2`
```cure
take(n: Int, list: List(T, m)) -> List(T, min(n, m)) when n >= 0
```
Takes the first n elements from a list.

**Example:**
```cure
take(2, [1, 2, 3, 4])    # Returns: [1, 2]
take(10, [1, 2])         # Returns: [1, 2]
take(0, [1, 2, 3])       # Returns: []
```

#### `drop/2`
```cure
drop(n: Int, list: List(T, m)) -> List(T, max(0, m-n)) when n >= 0
```
Drops the first n elements from a list.

**Example:**
```cure
drop(2, [1, 2, 3, 4])    # Returns: [3, 4]
drop(10, [1, 2])         # Returns: []
drop(0, [1, 2, 3])       # Returns: [1, 2, 3]
```

#### `zip/2`
```cure
zip(list1: List(T, n), list2: List(U, n)) -> List((T, U), n)
```
Combines two lists of equal length into a list of pairs.

**Example:**
```cure
zip([1, 2, 3], ["a", "b", "c"])  # Returns: [(1, "a"), (2, "b"), (3, "c")]
```

#### `unzip/1`
```cure
unzip(list: List((T, U), n)) -> (List(T, n), List(U, n))
```
Separates a list of pairs into two lists.

**Example:**
```cure
unzip([(1, "a"), (2, "b")])  # Returns: ([1, 2], ["a", "b"])
```

## Arithmetic Functions

### Basic Arithmetic

#### `abs/1`
```cure
abs(x: Int) -> Nat
abs(x: Float) -> Float when result >= 0.0
```
Returns the absolute value of a number.

**Example:**
```cure
abs(-42)      # Returns: 42
abs(3.14)     # Returns: 3.14
abs(-2.5)     # Returns: 2.5
```

#### `min/2`
```cure
min(x: T, y: T) -> T where T: Ord
```
Returns the smaller of two values.

**Example:**
```cure
min(5, 10)        # Returns: 5
min(-1, 3)        # Returns: -1
min(2.5, 1.8)     # Returns: 1.8
```

#### `max/2`
```cure
max(x: T, y: T) -> T where T: Ord
```
Returns the larger of two values.

**Example:**
```cure
max(5, 10)        # Returns: 10
max(-1, 3)        # Returns: 3
max(2.5, 1.8)     # Returns: 2.5
```

### Advanced Mathematical Functions

#### `sqrt/1`
```cure
sqrt(x: Float) -> Float when x >= 0.0, result >= 0.0
```
Returns the square root of a number.

**Example:**
```cure
sqrt(16.0)        # Returns: 4.0
sqrt(2.0)         # Returns: 1.414...
```

#### `pow/2`
```cure
pow(base: Float, exponent: Float) -> Float
```
Returns base raised to the power of exponent.

**Example:**
```cure
pow(2.0, 3.0)     # Returns: 8.0
pow(10.0, 0.5)    # Returns: 3.162... (sqrt(10))
```

#### `sin/1`, `cos/1`, `tan/1`
```cure
sin(x: Float) -> Float
cos(x: Float) -> Float  
tan(x: Float) -> Float
```
Trigonometric functions (angle in radians).

**Example:**
```cure
sin(0.0)          # Returns: 0.0
cos(0.0)          # Returns: 1.0
tan(0.0)          # Returns: 0.0
```

#### `log/1`, `log10/1`
```cure
log(x: Float) -> Float when x > 0.0    # Natural logarithm
log10(x: Float) -> Float when x > 0.0  # Base-10 logarithm
```
Logarithmic functions.

**Example:**
```cure
log(2.718...)     # Returns: 1.0 (approximately)
log10(100.0)      # Returns: 2.0
```

## String Functions

### String Operations

#### `string_length/1`
```cure
string_length(s: String) -> Nat
```
Returns the length of a string.

**Example:**
```cure
string_length("hello")    # Returns: 5
string_length("")         # Returns: 0
```

#### `string_concat/2`
```cure
string_concat(s1: String, s2: String) -> String
```
Concatenates two strings.

**Example:**
```cure
string_concat("hello", " world")  # Returns: "hello world"
string_concat("", "test")         # Returns: "test"
```

#### `substring/3`
```cure
substring(s: String, start: Nat, length: Nat) -> String
  when start + length <= string_length(s)
```
Extracts a substring.

**Example:**
```cure
substring("hello world", 0, 5)    # Returns: "hello"
substring("hello world", 6, 5)    # Returns: "world"
```

#### `string_split/2`
```cure
string_split(s: String, delimiter: String) -> List(String)
```
Splits a string by a delimiter.

**Example:**
```cure
string_split("a,b,c", ",")        # Returns: ["a", "b", "c"]
string_split("hello world", " ")  # Returns: ["hello", "world"]
```

#### `string_join/2`
```cure
string_join(strings: List(String), separator: String) -> String
```
Joins a list of strings with a separator.

**Example:**
```cure
string_join(["a", "b", "c"], ",")        # Returns: "a,b,c"
string_join(["hello", "world"], " ")     # Returns: "hello world"
```

### String Predicates

#### `string_contains/2`
```cure
string_contains(s: String, substring: String) -> Bool
```
Checks if a string contains a substring.

**Example:**
```cure
string_contains("hello world", "world")  # Returns: true
string_contains("hello", "xyz")          # Returns: false
```

#### `string_starts_with/2`
```cure
string_starts_with(s: String, prefix: String) -> Bool
```
Checks if a string starts with a prefix.

**Example:**
```cure
string_starts_with("hello world", "hello")  # Returns: true
string_starts_with("world", "hello")        # Returns: false
```

#### `string_ends_with/2`
```cure
string_ends_with(s: String, suffix: String) -> Bool
```
Checks if a string ends with a suffix.

**Example:**
```cure
string_ends_with("hello world", "world")    # Returns: true
string_ends_with("hello", "world")          # Returns: false
```

## Compiler API

### Parsing Functions

#### `cure_lexer:tokenize/1`
```erlang
tokenize(Input :: string()) -> {ok, [Token]} | {error, Reason}.
```
Tokenizes Cure source code.

**Example:**
```erlang
cure_lexer:tokenize("def add(x, y) = x + y").
% Returns: {ok, [{def,1},{identifier,1,"add"},...]}
```

#### `cure_parser:parse/1`
```erlang
parse(Tokens :: [Token]) -> {ok, AST} | {error, Reason}.
```
Parses tokens into an AST.

**Example:**
```erlang
{ok, Tokens} = cure_lexer:tokenize("def add(x, y) = x + y"),
cure_parser:parse(Tokens).
% Returns: {ok, #function{name="add", ...}}
```

#### `cure_parser:parse_file/1`
```erlang
parse_file(Filename :: string()) -> {ok, AST} | {error, Reason}.
```
Parses a Cure source file.

**Example:**
```erlang
cure_parser:parse_file("examples/simple.cure").
```

### Type Checking Functions

#### `cure_typechecker:check_program/1`
```erlang
check_program(AST :: term()) -> {ok, TypedAST} | {error, TypeErrors}.
```
Type-checks a program AST.

**Example:**
```erlang
{ok, AST} = cure_parser:parse_file("example.cure"),
cure_typechecker:check_program(AST).
```

#### `cure_types:infer_type/2`
```erlang
infer_type(Expression :: term(), Context :: term()) -> {Type, Constraints}.
```
Infers the type of an expression.

### Code Generation Functions

#### `cure_codegen:compile_program/1`
```erlang
compile_program(TypedAST :: term()) -> {ok, BeamBinary} | {error, Reason}.
```
Compiles a typed AST to BEAM bytecode.

**Example:**
```erlang
{ok, TypedAST} = cure_typechecker:check_program(AST),
cure_codegen:compile_program(TypedAST).
```

#### `cure_beam_compiler:compile_to_beam/1`
```erlang
compile_to_beam(ErlangForms :: [term()]) -> binary().
```
Compiles Erlang abstract forms to BEAM bytecode.

## Runtime API

### FSM Runtime Functions

#### `cure_fsm_runtime:spawn_fsm/1,2`
```erlang
spawn_fsm(Type :: atom()) -> pid().
spawn_fsm(Type :: atom(), InitData :: term()) -> pid().
```
Spawns a new FSM process.

#### `cure_fsm_runtime:send_event/2,3`
```erlang
send_event(FsmPid :: pid(), Event :: term()) -> ok.
send_event(FsmPid :: pid(), Event :: term(), Timeout :: integer()) -> ok | timeout.
```
Sends an event to an FSM.

#### `cure_fsm_runtime:get_state/1`
```erlang
get_state(FsmPid :: pid()) -> term().
```
Gets the current state of an FSM.

#### `cure_fsm_runtime:stop_fsm/1`
```erlang
stop_fsm(FsmPid :: pid()) -> ok.
```
Stops an FSM process.

### FSM Registration Functions

#### `cure_fsm_runtime:register_fsm_type/2`
```erlang
register_fsm_type(TypeName :: atom(), Module :: atom()) -> ok.
```
Registers an FSM type with the runtime.

#### `cure_fsm_runtime:get_fsm_types/0`
```erlang
get_fsm_types() -> [atom()].
```
Returns a list of registered FSM types.

## Error Handling

### Result Type

Many functions return a `Result(T, E)` type for error handling:

```cure
Result(T, E) = Ok(T) | Error(E)
```

**Usage Pattern:**
```cure
case divide(10.0, 2.0) do
  Ok(result) -> "Result: " ++ string_of_float(result)
  Error(msg) -> "Error: " ++ msg
end
```

### Exception Handling

For runtime errors, Cure integrates with BEAM's exception system:

```cure
def safe_operation() -> Result(T, String) =
  try
    risky_operation()
  catch
    error -> Error("Operation failed")
  end
```

## Performance Notes

### Function Call Overhead
- **Local calls**: ~10ns overhead
- **Module-qualified calls**: ~15ns overhead  
- **FSM event sends**: ~1μs including message passing

### Memory Usage
- **Lists**: 8 bytes per element + 8 bytes overhead
- **Strings**: 1 byte per character + overhead
- **FSM processes**: ~2KB per instance
- **Function closures**: 16-32 bytes depending on captured variables

### Optimization Guidelines

1. **Use tail recursion** for loops to avoid stack growth
2. **Prefer pattern matching** over conditional chains
3. **Use FSMs** for stateful concurrent logic
4. **Batch FSM events** when possible to reduce message passing overhead
5. **Use dependent types** to eliminate runtime checks

## Integration Examples

### Calling from Erlang

```erlang
% Assuming compiled Cure module 'math_utils'
1> math_utils:factorial(5).
120

2> math_utils:fibonacci(10).
55
```

### Calling from Elixir

```elixir
# Assuming compiled Cure module 'math_utils'
iex> :math_utils.factorial(5)
120

iex> :math_utils.fibonacci(10)
55
```

### Using with OTP

```erlang
% FSM as supervised process
{ok, _} = supervisor:start_child(MySup, #{
    id => traffic_light,
    start => {traffic_light_fsm, start, []},
    type => worker
}).
```

This API reference covers all the core functionality available in Cure. For more detailed examples and usage patterns, see the other documentation files in this directory.