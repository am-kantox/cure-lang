# Cure Standard Library

This directory contains the standard library for the Cure programming language, written entirely in Cure itself. The standard library provides essential functionality for data manipulation, mathematical operations, string processing, and FSM (Finite State Machine) operations.

## Overview

The Cure standard library is organized into several modules:

- **`std.cure`** - Main module that re-exports commonly used functions
- **`std/core.cure`** - Core types and fundamental operations  
- **`std/list.cure`** - Comprehensive list operations with dependent types
- **`std/math.cure`** - Mathematical functions and numerical operations
- **`std/string.cure`** - String manipulation and text processing
- **`std/fsm.cure`** - High-level FSM utilities and common patterns

## Core Features

### Types and Error Handling

The standard library provides robust error handling through `Result` and `Option` types:

```cure
import Std [Result, Option, ok, error, some, none]

def safe_divide(x: Float, y: Float): Result(Float, String) =
  if y == 0.0 then error("Division by zero")
  else ok(x / y)
  end

def find_item(list: List(T), predicate: T -> Bool): Option(T) =
  # Returns Some(item) if found, None otherwise
  find(list, predicate)
```

### List Operations

Comprehensive list processing with dependent type support:

```cure
import Std [map/2, filter/2, foldl/3, head/1, tail/1]

# Transform lists
let doubled = map([1, 2, 3, 4], fn(x) -> x * 2 end)
let evens = filter([1, 2, 3, 4, 5, 6], fn(x) -> x % 2 == 0 end)

# Aggregate data
let sum = foldl([1, 2, 3, 4, 5], 0, fn(x, acc) -> x + acc end)

# Safe operations
let maybe_first = safe_head([1, 2, 3])  # Returns Some(1)
let empty_first = safe_head([])         # Returns None
```

### Mathematical Operations

Mathematical functions with safe variants:

```cure
import Std [pi/0, sqrt/1, abs/1, safe_divide/2]
import Std.Math [sin/1, cos/1, factorial/1, gcd/2]

# Constants and basic operations
let circle_area = pi() * sqrt(16.0)
let distance = abs(-42)

# Safe operations that return Result types
let safe_result = safe_divide(10.0, 3.0)  # Returns Ok(3.333...)
let error_result = safe_divide(10.0, 0.0) # Returns Error("Division by zero")

# Advanced math
let angle = sin(pi() / 4.0)
let fact5 = factorial(5)        # 120
let common = gcd(48, 18)        # 6
```

### String Processing

Comprehensive string manipulation:

```cure
import Std [
  string_concat/2, split/2, trim/1, to_upper/1,
  contains/2, starts_with/2, words/1
]

let text = "  Hello, Cure Programming!  "
let cleaned = trim(text)                    # "Hello, Cure Programming!"
let upper = to_upper(cleaned)               # "HELLO, CURE PROGRAMMING!"
let word_list = words(cleaned)              # ["Hello,", "Cure", "Programming!"]

# String searching
if contains(text, "Cure") then
  print("Found Cure in the text!")
end
```

### FSM Operations

High-level FSM utilities and common patterns:

```cure
import Std [fsm_create/2, fsm_send_safe/2, create_counter/1]

# Create a counter FSM
match create_counter(0) do
  Ok(counter) ->
    # Send events to the FSM
    fsm_send_safe(counter, :increment)
    fsm_send_safe(counter, :increment)
    print("Counter operations complete")
    
  Error(err) ->
    print("Failed to create counter: " ++ err)
end

# Create custom FSMs
match fsm_create('MyStateMachine', initial_data) do
  Ok(fsm) -> 
    fsm_send_safe(fsm, :start)
    # ... more operations
  Error(err) ->
    print("FSM creation failed: " ++ err) 
end
```

## Module Structure

### Std.Core
- **Types**: `Result(T, E)`, `Option(T)`, `Ordering`
- **Functions**: Identity, composition, boolean operations, comparisons
- **Error Handling**: Result and Option manipulation functions

### Std.List  
- **Construction**: `cons/2`, `head/1`, `tail/1`, `length/1`
- **Transformation**: `map/2`, `filter/2`, `reverse/1`, `append/2`
- **Folding**: `foldl/3`, `foldr/3`, `reduce/2`, `scan/3`
- **Searching**: `find/2`, `elem/2`, `all/2`, `any/2`
- **Slicing**: `take/2`, `drop/2`, `split_at/2`
- **Zipping**: `zip/2`, `zip3/3`, `unzip/1`
- **Safe Operations**: `safe_head/1`, `safe_tail/1`, `safe_nth/2`

### Std.Math
- **Constants**: `pi/0`, `e/0`, `tau/0`  
- **Basic**: `abs/1`, `sign/1`, `min/2`, `max/2`
- **Rounding**: `round/1`, `floor/1`, `ceiling/1`
- **Exponential**: `exp/1`, `ln/1`, `sqrt/1`, `power/2`
- **Trigonometric**: `sin/1`, `cos/1`, `tan/1`, `asin/1`, etc.
- **Number Theory**: `gcd/2`, `lcm/2`, `factorial/1`, `fibonacci/1`
- **Statistical**: `mean/1`, `median/1`, `variance/1`, `stddev/1`
- **Safe Operations**: `safe_divide/2`, `safe_sqrt/1`, `safe_ln/1`

### Std.String
- **Properties**: `length/1`, `is_empty/1`
- **Construction**: `concat/2`, `join/2`, `repeat/2`
- **Conversion**: `to_upper/1`, `to_lower/1`, `capitalize/1`
- **Searching**: `contains/2`, `starts_with/2`, `ends_with/2`, `index_of/2`
- **Slicing**: `slice/3`, `take/2`, `drop/2`, `reverse/1`
- **Trimming**: `trim/1`, `trim_left/1`, `trim_right/1`
- **Splitting**: `split/2`, `split_lines/1`, `words/1`
- **Replacement**: `replace/3`, `replace_all/3`

### Std.FSM
- **Creation**: `create/2`, `start/1`, `start_with_data/2`, `stop/1`
- **State Queries**: `current_state/1`, `get_data/1`, `is_alive/1`
- **Event Handling**: `send_event/2`, `send_batch_events/2`
- **Monitoring**: `get_info/1`, `get_history/1`, `get_stats/1`
- **Patterns**: `create_counter/1`, `create_toggle/1`, `create_timer/2`

## Usage Examples

### Basic Usage

```cure
# Import the main standard library
import Std [map/2, filter/2, ok/1, error/1]

def process_numbers(numbers: List(Int)): Result(List(Int), String) =
  if is_empty(numbers) then
    error("Cannot process empty list")
  else
    let processed = numbers
      |> filter(fn(x) -> x > 0 end)
      |> map(fn(x) -> x * 2 end)
    ok(processed)
  end
```

### Advanced Usage

```cure
# Import specific modules for advanced operations
import Std.Math [sqrt/1, safe_divide/2, mean/1]
import Std.List [zip_with/3, foldl/3]

def calculate_distance(points: List({Float, Float})): Result(Float, String) =
  let distances = zip_with(points, tail(points), fn({x1, y1}, {x2, y2}) ->
    let dx = x2 - x1
    let dy = y2 - y1
    sqrt(dx * dx + dy * dy)
  end)
  
  match safe_divide(foldl(distances, 0.0, add), length(distances)) do
    Ok(avg_distance) -> ok(avg_distance)
    Error(err) -> error("Distance calculation failed: " ++ err)
  end
```

## Design Principles

1. **Type Safety**: Extensive use of dependent types and Result/Option types
2. **Functional Programming**: Pure functions, immutable data structures  
3. **Composability**: Functions designed to work well together
4. **Safety**: Safe operations that handle edge cases gracefully
5. **Performance**: Efficient implementations using tail recursion where possible
6. **Consistency**: Uniform API design across all modules

## Future Extensions

The standard library is designed to be extensible. Planned additions include:

- **Std.IO** - Input/output operations and file handling
- **Std.Concurrent** - Concurrency primitives and process management
- **Std.Json** - JSON parsing and serialization
- **Std.Http** - HTTP client and server utilities  
- **Std.Crypto** - Cryptographic functions
- **Std.Test** - Testing framework and assertions

## Contributing

When adding new functions to the standard library:

1. Follow the existing naming conventions
2. Include comprehensive type signatures
3. Provide safe variants for potentially failing operations
4. Add documentation comments explaining the function's purpose
5. Include usage examples in the `examples/` directory

## Implementation Notes

Many functions in the standard library are currently implemented with placeholder bodies that return default values. In a full implementation:

- Mathematical functions would call native implementations
- String operations would work with actual character data
- FSM operations would integrate with the runtime system
- I/O operations would interface with the operating system

The current implementation serves as a specification and foundation for the complete standard library.