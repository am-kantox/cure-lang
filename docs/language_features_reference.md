# Cure Language Features Reference

**Version**: Complete Language Feature Coverage  
**Last Updated**: October 7, 2025

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
  print("Result: " ++ show(result))
  ok

# Private function
defp helper(x: Int): String = int_to_string(x)
```

### Lambda Expressions
```cure
# Simple lambda
let double = fn(x) -> x * 2 end

# Multi-line lambda with if-then-else
let safe_div = fn(x, y) ->
  if y == 0 then error("Division by zero")
  else ok(x / y)
  end
end

# Lambda with multiple parameters
let fold_sum = foldl(numbers, 0, fn(x, acc) -> x + acc end)
```

### Pattern Matching
```cure
match expression do
  Ok(value) -> handle_success(value)
  Error(msg) -> handle_error(msg)
end

match list do
  [] -> "empty"
  [x] -> "single: " ++ show(x)
  [x | rest] -> "head: " ++ show(x) ++ ", rest: " ++ show(rest)
end

match option do
  Some(found) -> "Found: " ++ show(found)
  None -> "Not found"
end
```

### If-Then-Else Expressions
```cure
if condition then
  expression1
else
  expression2
end
```

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

## Data Types

### Primitive Types
- `Int`: Integer numbers
- `Float`: Floating-point numbers  
- `String`: Text strings
- `Bool`: Boolean values (`true`, `false`)
- `Atom`: Atomic values (`:atom_name`)
- `Binary`: Byte sequences
- `Unit`: Unit type for functions with no return value
- `Nat`: Natural numbers (Int >= 0)
- `Pos`: Positive integers (Int > 0)
- `Pid`: Process identifier

### Dependent Types
```cure
List(Int)           # List of integers
Result(Int, String) # Result with success type Int, error type String
Option(String)      # Optional string value
```

### Constructor Types
```cure
Ok(value)           # Success result
Error(message)      # Error result
Some(value)         # Present optional value
None                # Absent optional value
```

## Operators

### Binary Operators
- Arithmetic: `+`, `-`, `*`, `/`, `%`
- Comparison: `==`, `!=`, `<`, `>`, `<=`, `>=`
- String: `++` (concatenation)
- List: `::` (cons operator)
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
```cure
{}                    # Empty tuple (Unit)
{42}                  # Single element tuple
{1, "hello", true}    # Multi-element tuple
{:ok, "success"}      # Tagged tuple
{:error, "failed"}    # Error tuple
```

### Atoms
```cure
:atom_name
:increment
:ok
```

## Process-Oriented Programming

### Process Definitions
```cure
# Process function
process counter_server(initial: Int) do
  def loop(count: Int) do
    receive do
      {:increment} -> loop(count + 1)
      {:decrement} -> loop(count - 1)
      {:get, from: Pid} -> 
        send(from, {:count, count})
        loop(count)
      {:stop} -> :ok
    end
  end
  
  loop(initial)
end

# Spawn a process
let counter = spawn(counter_server, [0])
```

### Message Passing
```cure
# Send message to process
send(counter, {:increment})
send(counter, {:get, self()})

# Receive messages
receive do
  {:count, value} -> print("Count: " ++ show(value))
  {:error, msg} -> print("Error: " ++ msg)
end
```

## Finite State Machines

```cure
# FSM definition
fsm tcp_connection do
  # State declarations
  states: [Closed, Listen, SynSent, Established]
  
  # Initial state
  initial: Closed
  
  # State definitions with transitions
  state Closed do
    event(:listen) -> Listen
    event(:connect) -> SynSent
  end
  
  state Listen do
    event(:syn_received) -> SynSent
    event(:close) -> Closed
  end
  
  state Established do
    event(:fin_received) -> Closed
    event({:data, payload: Binary}) -> Established
  end
end

# Using FSM
let conn = fsm_spawn(tcp_connection)
fsm_send(conn, :listen)
```

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
    "Hello, adult #{name}!"
  Person{name: name} ->
    "Hello, young #{name}!"
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

### Case Expressions
```cure
# Case expression (alternative to match)
case expression do
  Ok(value) -> handle_success(value)
  Error(msg) -> handle_error(msg)
end

case list do
  [] -> "empty"
  [x] -> "single: " ++ show(x)
  [x | rest] -> "head: " ++ show(x)
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
  if input < 0 then
    error("Negative input not allowed")
  else
    ok(input * 2)
  end
```

### Option Types
```cure
def find_item(list: List(String), target: String): Option(String) =
  case search(list, target) of
    found when found != "" -> some(found)
    _ -> none
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
  if y == 0.0 then
    error("Division by zero")
  else
    ok(x / y)
  end
```

### Pattern Matching
Prefer pattern matching over conditional logic:
```cure
# Good
match result do
  Ok(value) -> use_value(value)
  Error(msg) -> handle_error(msg)
end

# Less preferred
if is_ok(result) then
  use_value(unwrap(result))
else
  handle_error(get_error(result))
end
```

## Type System Features

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

## Compilation and Runtime

### Compilation Pipeline
1. **Source** → **Tokens** (Lexer)
2. **Tokens** → **AST** (Parser) 
3. **AST** → **Typed AST** (Type Checker)
4. **Typed AST** → **Core IR** (Desugaring)
5. **Core IR** → **BEAM Bytecode** (Code Generator)

### BEAM Integration
- **Processes**: Map to BEAM processes
- **FSMs**: Compile to gen_statem behaviors
- **Pattern Matching**: Use BEAM's efficient matching
- **Tail Calls**: Leverage BEAM's tail call optimization
- **Hot Code Loading**: Support BEAM's code upgrade mechanisms
- **Distribution**: Transparent distribution across nodes

---

This reference covers all currently implemented and planned language features, providing a comprehensive overview of Cure's capabilities including dependent types, process-oriented programming, and finite state machines.
