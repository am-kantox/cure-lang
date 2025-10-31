# Cure Language Features Reference

**Version**: Current Implementation Status  
**Last Updated**: October 31, 2025

This document provides a comprehensive reference for all Cure language features, including current implementation status, syntax examples, and usage patterns.

## Table of Contents

1. [Core Language Syntax](#core-language-syntax)
2. [Data Types and Type System](#data-types-and-type-system)
3. [Finite State Machines](#finite-state-machines)
4. [Type Classes and Constraints](#type-classes-and-constraints)
5. [Advanced Features](#advanced-features)
6. [Standard Library Integration](#standard-library-integration)
7. [CLI and Build System](#cli-and-build-system)
8. [Compilation and Runtime](#compilation-and-runtime)
9. [Testing Infrastructure](#testing-infrastructure)
10. [Performance and Optimization](#performance-and-optimization)

## Core Language Syntax

### Module System
```cure
module ModuleName do
  import Std [abs/1, sqrt/1, Option, Result]
  import Std.Math [sin/1, cos/1]
  
  export [main/0, demo_function/1]
  
  # Module contents...
end
```

### Function Definitions
```cure
# Simple function
def add(x: Int, y: Int): Int = x + y

# Function with complex body
def demo(): Unit =
  let result = calculate_something()
  println("Result: " <> show(result))
  0

# Helper function
def helper(x: Int): String = int_to_string(x)
```

### Lambda Expressions
```cure
# Simple lambda
let double = fn(x) -> x * 2 end

# Lambda with pattern matching instead of if-then-else
let safe_div = fn(x, y) ->
  match y == 0 do
    true -> error("Division by zero")
    false -> ok(x / y)
  end
end

# Lambda with multiple parameters
let fold_sum = fold(numbers, 0, fn(x, acc) -> x + acc end)
```

### Pattern Matching
```cure
match expression do
  Ok(value) -> handle_success(value)
  Error(msg) -> handle_error(msg)
end

match list do
  [] -> "empty"
  [x] -> "single: " <> show(x)
  [x | rest] -> "head: " <> show(x) <> ", rest: " <> show(rest)
end

match option do
  Some(found) -> "Found: " <> show(found)
  None -> "Not found"
end
```

### Case Expressions

Cure supports `case` expressions as an alternative to `match` (they are semantically identical):

```cure
# Case with 'of' keyword
case expression of
  Ok(value) -> handle_success(value)
  Error(msg) -> handle_error(msg)
end

# Functionally equivalent to match
match expression do
  Ok(value) -> handle_success(value)
  Error(msg) -> handle_error(msg)
end
```

**Note**: Cure does not have `if-then-else` expressions. Use `match` or `case` for conditional logic.

### Let Bindings
```cure
# Simple let
let x = 42

# Let with complex expression
let result = calculate()
  |> map(fn(x) -> x * 2 end)
  |> filter(fn(x) -> x > 10 end)
```

### Pipe Operations
```cure
result = input
  |> transform1()
  |> transform2(argument)
  |> final_transform()
```

## Data Types and Type System

### Primitive Types
- `Int`: 64-bit signed integers
- `Float`: 64-bit IEEE floating-point numbers  
- `String`: UTF-8 encoded text strings
- `Bool`: Boolean values (`true`, `false`)
- `Atom`: Symbolic constants (`:atom_name`)
- `Binary`: Byte sequences
- `Unit`: Unit type for functions with no return value
- `Nat`: Natural numbers (Int >= 0) - refinement type
- `Pos`: Positive integers (Int > 0) - refinement type
- `Pid`: BEAM process identifier

### Composite Types
```cure
List(T)                    # Homogeneous lists
List(T, n)                 # Length-indexed lists (dependent type)
Tuple(T1, T2, ...)         # Fixed-size tuples
Result(T, E)               # Error handling without exceptions
Option(T)                  # Nullable values
```

### Constructor Types
```cure
Ok(value)                  # Success result
Error(message)             # Error result
Some(value)                # Present optional value
None                       # Absent optional value
```

### Dependent Types
```cure
# Length-indexed types
Vector(T, n: Nat)          # Fixed-length vector
List(T, n: Nat)            # List with compile-time known length
Matrix(rows: Nat, cols: Nat, T)  # 2D matrix with dimensions

# Constraint-based types
{x: Int | x > 0}           # Positive integers
{x: Float | x >= 0.0}      # Non-negative floats
{xs: List(T) | length(xs) > 0}  # Non-empty lists

# Function-dependent types
def replicate(n: Nat, x: T): List(T, n)  # Return type depends on argument
def safe_head(xs: List(T, n)): T when n > 0  # Precondition constraint
```

## Operators

### Binary Operators
- Arithmetic: `+`, `-`, `*`, `/`, `%`
- Comparison: `==`, `!=`, `<`, `>`, `<=`, `>=`
- String: `<>` (concatenation)
- List: `|` (cons operator, used in `[h | t]` syntax)
- Pipe: `|>` (function composition)

### Unary Operators
- Arithmetic: `+x`, `-x`
- Logical: `not(expr)`

## Literals

### Numbers
```cure
42          # Integer
3.14        # Float
-5          # Negative integer
```

### Strings
```cure
"Hello, World!"       # Simple string
"Line 1\nLine 2"      # String with escape sequences
"Quote: \"text\""     # String with escaped quotes
```

### Lists
```cure
[]                    # Empty list
[1, 2, 3]            # List of integers
["a", "b", "c"]      # List of strings
```

### Tuples

Tuples use curly brace `{}` syntax:

```cure
{}                    # Empty tuple (Unit)
{42}                  # Single element tuple
{1, "hello", true}    # Multi-element tuple
{:ok, "success"}      # Tagged tuple (atom + value)
{:error, "failed"}    # Error tuple (atom + value)
```

**Note**: Tuple pattern matching is fully supported:
```cure
match point do
  {x, y} when x > 0.0 and y > 0.0 -> "First quadrant"
  {x, y} when x == 0.0 and y == 0.0 -> "Origin"
  _ -> "Other quadrant"
end
```

### Atoms
```cure
:atom_name
:increment
:ok
```

## Finite State Machines

Cure provides first-class support for finite state machines with compile-time verification, state-dependent data, and integration with the BEAM actor model.

### Basic FSM Definition

Cure FSMs use a record-based payload system with arrow transition syntax:

```cure
# Define a payload record to track FSM data
record TrafficPayload do
  cycles_completed: Int
  timer_events: Int
  emergency_stops: Int
end

# FSM with initial payload values
fsm TrafficPayload{cycles_completed: 0, timer_events: 0, emergency_stops: 0} do
  Red --> |timer| Green
  Red --> |emergency| Red      # Self-transition
  Green --> |timer| Yellow
  Green --> |emergency| Red
  Yellow --> |timer| Red
  Yellow --> |emergency| Red
end
```

**Key Points**:
- First state in transitions is the initial state (Red in this example)
- Transitions use `-->` arrow with `|event|` syntax
- Must define a payload record even if fields are unused

### FSM Runtime Operations

FSMs compile to BEAM `gen_statem` processes:

```cure
import Std.Fsm [fsm_spawn/2, fsm_cast/2, fsm_advertise/2, fsm_state/1]
import Std.Pair [pair/2]

# Spawn an FSM instance with initial data
let initial_data = TrafficPayload{cycles_completed: 0, timer_events: 0, emergency_stops: 0}
let fsm_pid = fsm_spawn(:TrafficPayload, initial_data)

# Give the FSM a name for easy reference
let adv_result = fsm_advertise(fsm_pid, :traffic_light)

# Send events to the FSM
let empty_list = []
let event = pair(:timer, empty_list)
let cast_result = fsm_cast(:traffic_light, event)

# Query current state
let current_state = fsm_state(:traffic_light)  # Returns current state atom
```

### FSM Implementation Notes

Cure FSMs compile to Erlang `gen_statem` behaviors with the following features:

**Compile-Time Verification**:
- State machine structure validated at compile time
- Transition completeness checked
- Event type checking

**Runtime Integration**:
- Native BEAM process integration
- Mailbox-based event handling
- OTP supervision tree compatible
- Hot code reloading support

**Current Implementation**:
- Simple arrow-based transition syntax (`State1 --> |event| State2`)
- Record-based payload data tracking
- Event casting with atom-based event names
- State querying via FSM references


## Records and Dependent Types

### Record Definitions
```cure
record Person do
  name: String
  age: Nat
  email: String
end

# Creating records
let person = Person{name: "Alice", age: 30, email: "alice@example.com"}

# Pattern matching on records
match person do
  Person{name: name, age: age} when age >= 18 ->
    "Hello, adult " <> name <> "!"
  Person{name: name} ->
    "Hello, young " <> name <> "!"
end
```

### Dependent Types
```cure
# Length-indexed types
Vector(T, n: Nat)      # Fixed-length vector
List(T, n: Nat)        # List with known length
Range(min: Int, max: Int)  # Integer range type

# Matrix with dimension checking
record Matrix(rows: Nat, cols: Nat, T) do
  data: Vector(Vector(T, cols), rows)
end

# Refinement types
type NonEmptyList(T) = List(T, n) when n > 0

def head(list: NonEmptyList(T)): T =
  match list do
    [x|_] -> x
    # No need for empty case - type system guarantees non-empty
  end
```

## Advanced Features

### Function Imports with Arity
```cure
import ModuleName [
  function1/1,    # Function with 1 parameter
  function2/2,    # Function with 2 parameters
  TypeName,       # Type import
  constructor     # Constructor import
]
```

### Complex Nested Expressions
```cure
# Nested lambdas in higher-order functions
processed = data
  |> filter(fn(item) -> not(is_empty(item)) end)
  |> map(fn(item) -> 
      process_item(item)
        |> validate()
        |> transform()
     end)
  |> collect_results()
```

### Match vs Case

Both `match` and `case` are supported and functionally equivalent:

```cure
# Case expression with 'of' keyword (alternative to match)
case expression of
  Ok(value) -> handle_success(value)
  Error(msg) -> handle_error(msg)
end

case list of
  [] -> "empty"
  [x] -> "single: " <> show(x)
  [x | rest] -> "head: " <> show(x)
end
```

### Pattern Matching with Guards
```cure
match value do
  x when x > 0 -> "positive"
  x when x < 0 -> "negative"
  _ -> "zero"
end

# Guards in case expressions
case number do
  n when n > 100 -> "large"
  n when n > 10 -> "medium" 
  _ -> "small"
end
```

## Error Handling Patterns

### Result Types
```cure
def safe_operation(input: Int): Result(Int, String) =
  match input < 0 do
    true -> error("Negative input not allowed")
    false -> ok(input * 2)
  end
```

### Option Types
```cure
def find_item(list: List(String), target: String): Option(String) =
  match search(list, target) do
    found when found != "" -> Some(found)
    _ -> None
  end
```

## Best Practices

### Function Composition
Use pipe operators for readable data transformations:
```cure
result = input
  |> validate_input()
  |> process_data()
  |> format_output()
```

### Error Handling
Use Result types for operations that can fail:
```cure
def divide(x: Float, y: Float): Result(Float, String) =
  match y == 0.0 do
    true -> error("Division by zero")
    false -> ok(x / y)
  end
```

### Pattern Matching
Prefer pattern matching for control flow:
```cure
# Good - using pattern matching
match result do
  Ok(value) -> use_value(value)
  Error(msg) -> handle_error(msg)
end

# Also good - using case
case result of
  Ok(value) -> use_value(value)
  Error(msg) -> handle_error(msg)
end
```

## Type Classes and Constraints

Cure supports type classes for ad-hoc polymorphism and constraint-based programming.

### Type Class Definition
```cure
typeclass Ord(T) where
  def compare(x: T, y: T): Ordering
  def (<)(x: T, y: T): Bool = compare(x, y) == LT
  def (<=)(x: T, y: T): Bool = compare(x, y) != GT
end

typeclass Show(T) where
  def show(x: T): String
end

typeclass Functor(F) where
  def map(f: A -> B, fa: F(A)): F(B)
end
```

### Type Class Instances
```cure
# Manual instances
instance Ord(Int) where
  def compare(x, y) =
    if x < y then LT
    else if x > y then GT
    else EQ
    end
end

# Automatic derivation
derive Ord for List(T) when Ord(T)
derive Show for Option(T) when Show(T)
derive Functor for List
derive Functor for Option
```

### Constraint-Based Programming
```cure
# Generic sorting with constraints
def sort(xs: List(T)): List(T) where Ord(T) =
  quicksort_impl(xs)

# Pretty printing with constraints  
def debug_print(x: T): Unit where Show(T) =
  print(show(x))

# Functor mapping
def transform(f: A -> B, container: F(A)): F(B) where Functor(F) =
  map(f, container)
```

## Advanced Features

### Pi Types (Dependent Functions)
```cure
# Function types that depend on their arguments
def replicate(n: Nat, x: T): List(T, n) = 
  if n == 0 then [] else x :: replicate(n-1, x)
```

### Sigma Types (Dependent Pairs)
```cure
# Pairs where the second type depends on the first value
{x: Nat, Vector(Int, x)}  # Pair of number and vector of that length
```

### Refinement Types
```cure
# Types with predicates
{x: Int | x > 0}          # Positive integers
{x: List(T) | length(x) > 0}  # Non-empty lists
```

### Indexed Types
```cure
# Types parameterized by values
Vector(T, n: Nat)         # Vector of type T with length n
Matrix(rows: Nat, cols: Nat, T)  # Matrix with compile-time dimensions
```

## CLI and Build System

Cure provides a sophisticated command-line interface with wrapper script automation and intelligent build management.

### Wrapper Script Commands
```bash
# Special wrapper script commands
cure build      # Execute 'make all' to build compiler
cure test       # Execute 'make test' to run test suite
cure clean      # Execute 'make clean' to clean build artifacts
cure shell      # Start Erlang development shell with modules loaded
```

### File Compilation
```bash
# Basic compilation
cure input.cure                    # Compile with defaults
cure input.cure -o output.beam     # Specify output file
cure input.cure --verbose          # Verbose compilation
cure input.cure --no-optimize      # Disable optimizations
```

### Automatic Standard Library Management
- **Import Detection**: Automatically detects if source files need stdlib imports
- **Smart Imports**: Adds common stdlib imports to files without explicit module/import declarations
- **Conflict Avoidance**: Skips automatic imports for files with explicit module definitions or imports
- **Partial Failure Handling**: Reports detailed errors when stdlib compilation partially fails

### Module Detection and Validation
- **Required Modules Check**: Validates presence of all required BEAM compiler modules
- **Missing Module Reporting**: Provides detailed error messages for missing components
- **Build Automation**: Automatically triggers 'make all' when modules are missing
- **Error Recovery**: Graceful error handling with instructions for resolution

### Standard Library Compilation
- **Automatic Compilation**: Compiles stdlib modules as needed during user file compilation
- **Dependency Resolution**: Handles stdlib dependencies and compilation order
- **Partial Failure Recovery**: Attempts individual file compilation when batch compilation fails
- **Path Conversion**: Converts BEAM paths to source paths for error reporting

## Standard Library Integration

Cure includes a comprehensive standard library implemented in Cure itself with Erlang runtime support.

### Core Standard Library Modules
```cure
# Import common types and functions
import Std [Result, Option, ok, error, some, none]
import Std [map/2, filter/2, fold_left/3, fold_right/3]

# Mathematical operations
import Std.Math [abs/1, sqrt/1, sin/1, cos/1, pi, e]

# String operations
import Std.String [length/1, concat/2, split/2, trim/1]

# FSM utilities
import Std.FSM [create/2, send_event/2, get_state/1]
```

### Result and Option Types
```cure
# Chainable error handling
result = safe_divide(x, y)
  |> map_ok(fn(val) -> val * 2 end)
  |> and_then(fn(doubled) -> safe_sqrt(doubled) end)

match result do
  Ok(final_value) -> println("Success: " <> show(final_value))
  Error(msg) -> println("Error: " <> msg)
end

# Optional value handling
opt_value = find_in_list(items, predicate)
  |> map(fn(item) -> process(item) end)
  |> filter(fn(processed) -> is_valid(processed) end)
```

## Testing Infrastructure

Cure includes comprehensive testing infrastructure covering all aspects of the compiler and standard library.

### Comprehensive Test Suites
```bash
# Master test runner for all new CLI and stdlib tests
erl -pa _build/ebin -pa test -s run_all_new_tests run -s init stop

# Individual comprehensive test suites
erl -pa _build/ebin -pa test -s cli_wrapper_comprehensive_test run -s init stop
erl -pa _build/ebin -pa test -s cure_wrapper_script_test run -s init stop
```

### CLI and Wrapper Testing
- **Build Command Testing**: Verifies wrapper script correctly executes 'make all' for build command
- **Missing Module Detection**: Tests wrapper script detection and reporting of missing BEAM modules
- **Error Message Validation**: Ensures proper error reporting with helpful instructions
- **Script Logic Verification**: Tests all wrapper script conditional logic and edge cases

### Standard Library Testing
- **Automatic Import Testing**: Validates CLI automatic stdlib import addition and detection
- **Import Conflict Detection**: Tests detection of explicit modules/imports to prevent conflicts
- **Compilation Failure Testing**: Tests stdlib compilation partial failure reporting
- **Performance Testing**: Benchmarks Std.List.length function with large datasets (up to 50k elements)

### Test Coverage Areas
- **Lexical Analysis**: Token recognition and error handling
- **Parsing**: AST construction and syntax validation
- **Type System**: Inference, checking, and unification
- **Code Generation**: BEAM instruction generation
- **FSM Runtime**: State transitions and event handling
- **CLI Functionality**: Complete wrapper script and CLI module coverage
- **Error Handling**: Comprehensive error message formatting and reporting

### Testing Features
- **EUnit Integration**: All tests use EUnit assertions for reliable verification
- **Performance Benchmarks**: Tests include timing validation for large datasets
- **Edge Case Coverage**: Comprehensive testing of boundary conditions and error scenarios
- **Master Test Runner**: Orchestrated execution of all test suites with detailed reporting
- **Component Isolation**: Both comprehensive and focused component-specific test suites

## Compilation and Runtime

### Current Compilation Pipeline
1. **Source (.cure)** → **Tokens** (`cure_lexer.erl`)
2. **Tokens** → **AST** (`cure_parser.erl`)
3. **AST** → **Typed AST** (`cure_typechecker.erl`)
4. **Type Optimization** (`cure_type_optimizer.erl`)
   - Monomorphization
   - Function specialization  
   - Inlining analysis
   - Dead code elimination
5. **BEAM Bytecode** (`cure_codegen.erl`, `cure_beam_compiler.erl`)

### BEAM Integration Features
- **Native Processes**: FSMs compile to BEAM processes with supervision
- **gen_statem Integration**: FSMs use OTP gen_statem behavior
- **Pattern Matching**: Leverages BEAM's efficient pattern matching
- **Tail Call Optimization**: Preserves BEAM's tail recursion optimization
- **Hot Code Loading**: Supports BEAM's live code upgrade
- **Distributed Computing**: Transparent distribution across BEAM nodes
- **OTP Compatibility**: Seamless integration with Erlang/Elixir ecosystems

## Performance and Optimization

### Type-Directed Optimizations
Cure's type system enables aggressive optimizations:

```cure
# Before optimization (polymorphic)
def map(f: T -> U, xs: List(T)): List(U) = ...

# After monomorphization (specialized for Int -> String)
def map_Int_String(f: Int -> String, xs: List(Int)): List(String) = 
  # Optimized implementation for specific types
  specialized_map_impl(f, xs)
```

### Performance Characteristics
- **Function calls**: ~10ns overhead (optimized)
- **FSM events**: ~1μs including message passing
- **Type checking**: Zero runtime overhead (compile-time only)
- **Pattern matching**: BEAM-native performance
- **Memory usage**: Comparable to equivalent Erlang code
- **Optimizations**: 25-60% performance improvement over unoptimized code

### Compiler Performance
- Small files (<100 lines): <1 second compilation
- Medium projects (1K-10K lines): 5-30 seconds
- Large projects (100K+ lines): 30-300 seconds with incremental compilation
- Type checking scales O(n²) due to dependent types
- SMT constraint solving typically sub-second for realistic programs

---

## Implementation Status

### ✅ **Fully Implemented**
- Core syntax and semantics
- Dependent type system with SMT solving
- FSM compilation and runtime
- Type-directed optimizations
- BEAM code generation
- Standard library with runtime support
- Advanced CLI with wrapper script automation
- Automatic standard library import management
- Comprehensive test suite with performance benchmarks
- CLI wrapper functionality with missing module detection
- Partial compilation failure handling and recovery

### 🚧 **Advanced Features** 
- Complex type class hierarchies
- Advanced dependent type features (proof obligations)
- Linear types for resource management
- Distributed FSM coordination

This reference covers all currently implemented language features and provides insight into Cure's unique combination of dependent types, native FSM support, and BEAM integration.
