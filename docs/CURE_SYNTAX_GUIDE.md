# Cure Language Syntax Guide

**Based on**: Actual Cure implementation (Standard Library v1.0)  
**Purpose**: Reference for creating correct Cure examples  
**Last Updated**: October 30, 2025

---

## 1. Module Structure

Every Cure file should define a module:

```cure
module ModuleName do
  export [function_name/1, TypeName]
  
  # Module contents
end
```

### Exports

Export declarations specify what's public:

```cure
export [
  function_name/1,    # Function with arity
  TypeName,           # Type constructor
  constructor_name    # Data constructor
]
```

### Imports

Import from other modules (including standard library):

```cure
import Std.Core [Result, Option, ok/1, error/1]
import Std.List [map/2, filter/2, fold/3]
import Std.Io [print/1, println/1]
```

---

## 2. Comments

Single-line comments only:

```cure
# This is a comment
```

---

## 3. Type Definitions

### Type Aliases with Sum Types

```cure
type Result(T, E) = Ok(T) | Error(E)
type Option(T) = Some(T) | None
type Ordering = Lt | Eq | Gt
```

### Record Types

Records define structured data with named fields:

```cure
record RecordName do
  field1: Type1
  field2: Type2
  field3: Type3
end
```

#### Record with Type Parameters

```cure
record Point(T) do
  x: T
  y: T
end
```

#### Record Construction

```cure
# Create a record instance
let point = Point{x: 3.0, y: 4.0}
let payload = TrafficPayload{cycles_completed: 0, timer_events: 0, emergency_stops: 0}
```

#### Record Pattern Matching

```cure
# Match and extract fields
match point do
  Point{x: x, y: y} when x == 0.0 and y == 0.0 ->
    "Origin"
  Point{x: x, y: y} when x > 0.0 and y > 0.0 ->
    "First quadrant"
  Point{x: _, y: y} when y == 0.0 ->
    "On X-axis"
end

# Partial field matching (other fields ignored)
match person do
  Person{age: age, score: score} when age < 18 and score >= 90 ->
    "Outstanding young achiever"
end
```

---

## 4. Function Definitions

### Basic Function Syntax

```cure
def function_name(param1: Type1, param2: Type2): ReturnType =
  expression
```

### Function with Match Expression

```cure
def length(list: List(T)): Nat =
  match list do
    [] -> Zero
    [_ | t] -> Succ(length(t))
  end
```

### Functions with Let Bindings

```cure
def filter(list: List(T), predicate: T -> Bool): List(T) =
  match list do
    [] -> []
    [h | t] -> 
      let filtered_tail = filter(t, predicate)
      match predicate(h) do
        true -> [h | filtered_tail]
        false -> filtered_tail
      end
  end
```

### Lambda Functions

Lambda syntax: `fn(params) -> expression end`

```cure
# Simple lambda
let double = fn(x) -> x * 2 end

# Lambda with multiple params
let add = fn(x, y) -> x + y end

# Curried function application
let partial_func = func(h)
partial_func(fold(t, init, func))
```

---

## 5. Pattern Matching

### Match Expression Structure

```cure
match value do
  pattern1 -> result1
  pattern2 -> result2
  _ -> default_result
end
```

### Pattern Guards

Guards allow additional conditions on patterns using `when`:

```cure
match value do
  x when x < 0 -> "Negative"
  x when x == 0 -> "Zero"
  x when x > 0 -> "Positive"
end

# Multiple conditions with logical operators
match n do
  x when x >= 10 and x <= 20 -> "In range"
  x when x < 10 or x > 20 -> "Out of range"
end

# Guards with record patterns
match point do
  Point{x: x, y: y} when x > 0.0 and y > 0.0 ->
    "First quadrant"
  Point{x: x, y: _} when x == 0.0 ->
    "On Y-axis"
end
```

### List Patterns

```cure
match list do
  [] -> # empty list
  [h | t] -> # head and tail
  [a, b, c] -> # exact length (if supported)
end
```

### Constructor Patterns

```cure
match result do
  Ok(value) -> # success case
  Error(err) -> # error case
end

match option do
  Some(value) -> # present
  None -> # absent
end
```

### Nested Match

```cure
match list do
  [] -> []
  [h | t] ->
    match predicate(h) do
      true -> [h | filtered_tail]
      false -> filtered_tail
    end
end
```

---

## 6. Type Annotations

### Function Types

Arrow notation for function types:

```cure
# Function taking T, returning U
T -> U

# Function taking two params
T -> U -> V

# Can be curried
def func(x: T): U -> V =
  fn(y) -> result end
```

### Polymorphic Types

Generic type parameters:

```cure
def identity(x: T): T = x
def map(list: List(T), f: T -> U): List(U) = ...
```

---

## 7. Literals and Basic Types

### Primitives

```cure
42              # Int
3.14            # Float
"hello"         # String
true            # Bool
false           # Bool
:atom_name      # Atom
```

### Lists

```cure
[]              # Empty list
[1, 2, 3]       # List of integers
[h | t]         # Cons pattern/constructor
```

### Tuples (Limited Support)

Check actual implementation before using tuples extensively.

---

## 8. Operators

### Arithmetic

```cure
x + y           # Addition
x - y           # Subtraction
x * y           # Multiplication
x / y           # Division (may be integer division)
```

### Comparison

```cure
x == y          # Equality
x != y          # Inequality
x < y           # Less than
x > y           # Greater than
x <= y          # Less than or equal
x >= y          # Greater than or equal
```

### List Construction

```cure
[element | list]    # Cons (prepend)
```

### String Concatenation

```cure
str1 <> str2    # Diamond operator for string concatenation
```

---

## 9. Let Bindings

Simple let syntax:

```cure
let variable = expression
let result = function_call()
```

**Note**: Use `in` for scoped let expressions (check if implemented):

```cure
let x = 5 in x + 10
```

---

## 10. Special Constructs

### Curify (Erlang FFI)

Declare Erlang FFI functions:

```cure
curify function_name(param: Type): ReturnType = {module, function, arity}
```

Example:

```cure
curify print_raw(format: String, args: List(String)): Unit = {io, format, 2}
```

### Nat Type and Peano Numbers

Natural numbers use Peano encoding:

```cure
Zero            # Zero
Succ(n)         # Successor of n
```

Example:

```cure
def length(list: List(T)): Nat =
  match list do
    [] -> Zero
    [_ | t] -> Succ(length(t))
  end
```

---

## 11. FSM Syntax

FSMs are defined with an initial payload record and transition arrows:

```cure
# Define a payload record for FSM state tracking
record PayloadName do
  field1: Type1
  field2: Type2
end

# FSM definition with initial payload values
fsm PayloadName{field1: value1, field2: value2} do
  State1 --> |event1| State2
  State1 --> |event2| State1
  State2 --> |event3| State1
end
```

### FSM Example: Turnstile

```cure
record TurnstilePayload do
  coins_inserted: Int
  people_passed: Int
  denied_attempts: Int
end

fsm TurnstilePayload{coins_inserted: 0, people_passed: 0, denied_attempts: 0} do
  Locked --> |coin| Unlocked
  Locked --> |push| Locked
  Unlocked --> |coin| Unlocked
  Unlocked --> |push| Locked
end
```

### FSM Runtime Operations

```cure
import Std.Fsm [fsm_spawn/2, fsm_cast/2, fsm_advertise/2, fsm_state/1]
import Std.Pair [pair/2]

# Spawn an FSM instance
let fsm_pid = fsm_spawn(:PayloadName, initial_data)

# Give it a name
let adv_result = fsm_advertise(fsm_pid, :fsm_name)

# Send an event (with empty data list)
let empty_list = []
let event = pair(:event_name, empty_list)
let cast_result = fsm_cast(:fsm_name, event)

# Get current state
let current_state = fsm_state(:fsm_name)
```

**Key Points**:
- First state in transitions is the initial state
- Events are atoms (`:event_name`)
- Transitions use `-->` and `|event|` syntax
- Must define a payload record even if empty

---

## 12. Common Patterns from Std Library

### Result/Option Handling

```cure
match result do
  Ok(value) -> # handle success
  Error(err) -> # handle error
end

match option do
  Some(value) -> # handle present value
  None -> # handle absence
end
```

### Recursive List Processing

```cure
def map(list: List(T), f: T -> U): List(U) =
  match list do
    [] -> []
    [h | t] -> [f(h) | map(t, f)]
  end
```

### Tail Recursion with Accumulator

```cure
def reverse(list: List(T), acc: List(T)): List(T) =
  match list do
    [] -> acc
    [h | t] -> reverse(t, [h | acc])
  end
```

### Curried Functions

```cure
# Function returns another function
def flip(f: A -> B -> C): B -> A -> C =
  fn(b, a) -> 
    let g = f(a) in
    g(b)
  end
```

---

## 13. Key Syntactic Rules

1. **Module Required**: Every file needs a `module ModuleName do ... end`
2. **Type Annotations**: All function parameters and return types must be annotated
3. **Pattern Matching**: Use `match ... do ... end` blocks
4. **Lambdas**: Use `fn(params) -> body end` syntax
5. **Let Binding**: Simple `let name = value` without semicolons
6. **Function Application**: Standard `func(arg1, arg2)` syntax
7. **Comments**: Only `#` single-line comments
8. **Indentation**: Not significant (use `do ... end` blocks)

---

## 14. Things to AVOID (Not in Std Library)

Based on actual standard library, these features may not be implemented:

1. **Process definitions**: `process name(...) do ... end` - verify syntax
2. **Dependent types**: `Vector(T, n: Nat)` - may not fully work yet
3. **String interpolation**: `"text #{expr}"` - use `<>` for concatenation instead
4. **If-then-else**: May exist but std lib uses match expressions

---

## 15. Recommended Workflow

When creating examples:

1. Start with module definition
2. Import needed functions from Std library
3. Define types (sum types with constructors)
4. Define functions with explicit type signatures
5. Use pattern matching for control flow
6. Use lambdas for higher-order functions
7. Keep it simple - mirror std library style

---

## Example: Complete Module Template

```cure
module ExampleModule do
  export [
    main/0,
    helper_function/1
  ]
  
  # Import standard library functions
  import Std.Core [Result, ok/1, error/1]
  import Std.List [map/2, filter/2]
  import Std.Io [print/1]
  
  # Type definition
  type MyType(T) = Constructor1(T) | Constructor2(String)
  
  # Main function
  def main(): Unit =
    let result = helper_function(42)
    print("Done")
  
  # Helper with pattern matching
  def helper_function(value: Int): Result(String, String) =
    match value > 0 do
      true -> ok("positive")
      false -> error("non-positive")
    end
end
```

---

**This guide is based on actual working code in the Cure standard library. When in doubt, refer to `lib/std/` directory for real examples.**
