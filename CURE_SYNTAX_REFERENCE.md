# Cure Language Syntax Reference

**Version**: 1.0.0  
**Last Updated**: October 21, 2025  
**Status**: Complete Implementation with Runtime Verification  

This document provides a comprehensive reference for the Cure programming language syntax, covering all implemented features with practical examples and usage patterns.

## Table of Contents

1. [Overview](#overview)
2. [Module System](#module-system)
3. [Basic Syntax](#basic-syntax)
4. [Data Types](#data-types)
5. [Function Definitions](#function-definitions)
6. [Expressions](#expressions)
7. [Pattern Matching](#pattern-matching)
8. [Dependent Types](#dependent-types)
9. [Finite State Machines](#finite-state-machines)
10. [Process Definitions](#process-definitions)
11. [Standard Library Integration](#standard-library-integration)
12. [Grammar Reference](#grammar-reference)

## Overview

Cure is a strongly-typed, dependently-typed functional programming language for the BEAM virtual machine that combines advanced type system features with native finite state machine support and seamless BEAM ecosystem integration.

### Key Features
- **Dependent Types**: Advanced type system with SMT-based constraint solving
- **Native FSMs**: First-class finite state machines with compile-time verification
- **BEAM Integration**: Full compatibility with Erlang/OTP ecosystem
- **Pattern Matching**: Comprehensive pattern matching with exhaustiveness checking
- **Working Import System**: Complete module system with standard library integration ✅

## Module System

### Module Definition
```cure
module ModuleName do
  # Export declarations
  export [function_name/arity, TypeName, constructor]
  
  # Import statements
  import Std [Result, Option, print/1, show/1]
  import OtherModule [specific_function/2]
  
  # Module contents
  def function_name(param: Type): ReturnType = expression
end
```

### Import Statements ✅ **WORKING**
```cure
# Import entire module
import ModuleName

# Import specific functions with arity
import Std [print/1, show/1, map/2]

# Import types and constructors
import Std [Result, Option, ok, error, some, none]

# Import from submodules
import Std.List [fold/3, filter/2, length/1]
```

### Export Declarations
```cure
export [
  function_name/arity,    # Function with arity
  TypeName,               # Type name
  constructor,            # Constructor name
  private_helper/1        # Can export private functions
]
```

## Basic Syntax

### Comments
```cure
# Single line comment
# Comments use hash symbol and continue to end of line
```

### Identifiers
```cure
# Function and variable names
function_name
variable_name
_private_var
CamelCaseType

# Module-qualified identifiers
Module.function_name
Std.List.map
```

### Keywords
Reserved words in Cure:
```cure
def defp def_erl module import export fsm state states initial event
timeout match when if then else let in as do end fn process receive
send spawn record type and or not ok error true false
```

## Data Types

### Primitive Types
```cure
Int                    # Arbitrary precision integers
Float                  # Double precision floats  
String                 # UTF-8 strings
Bool                   # Boolean values (true/false)
Atom                   # Interned symbols (:atom_name)
Binary                 # Byte sequences
Unit                   # Unit type for functions with no meaningful return
Pid                    # BEAM process identifier
```

### Refinement Types
```cure
Nat                    # Natural numbers (Int >= 0)
Pos                    # Positive integers (Int > 0)
```

### Compound Types
```cure
List(T)                # Homogeneous lists
List(T, n: Nat)        # Length-indexed lists (dependent type)
Vector(T, n: Nat)      # Fixed-length vectors
{T1, T2, ...}          # Tuples
Result(T, E)           # Error handling type
Option(T)              # Optional values
```

### Type Constructors
```cure
# Result type constructors
Ok(value)              # Success result
Error(message)         # Error result

# Option type constructors  
Some(value)            # Present optional value
None                   # Absent optional value
```

### Dependent Types ✅ **WORKING**
```cure
# Length-parameterized types
Vector(T, n: Nat)                    # Vector of type T with length n
List(T, n: Nat)                      # List with compile-time known length
Matrix(rows: Nat, cols: Nat, T)      # 2D matrix with dimensions

# Constraint-based types
{x: Int | x > 0}                     # Positive integers
{x: Float | x >= 0.0}                # Non-negative floats
{xs: List(T) | length(xs) > 0}       # Non-empty lists

# Function-dependent types
def replicate(n: Nat, x: T): List(T, n)  # Return type depends on argument
def safe_head(xs: List(T, n)): T when n > 0  # Precondition constraint
```

## Function Definitions

### Basic Function Definitions
```cure
# Simple function
def add(x: Int, y: Int): Int = x + y

# Function with complex body
def greet(name: String): Unit =
  print("Hello, " ++ name ++ "!")
  ok

# Private function
defp helper_function(x: Int): String = show(x)
```

### Functions with Dependent Types
```cure
# Function with dependent return type
def replicate(n: Nat, x: T): List(T, n) = 
  if n == 0 then [] else x :: replicate(n-1, x)

# Function with constraints
def safe_divide(x: Int, y: Int): Int when y != 0 = x / y

# Function with guard constraints
def safe_head(list: List(T, n)): T when n > 0 =
  match list do
    [x|_] -> x
    # No need for empty case - type system prevents it
  end
```

### Erlang Interop Functions
```cure
# Direct Erlang code integration
def_erl system_info(key: Atom): String =
  "erlang:system_info(Key)"
```

### Lambda Expressions
```cure
# Simple lambda
let double = fn(x) -> x * 2 end

# Multi-line lambda
let safe_divide = fn(x, y) ->
  if y == 0 then error("Division by zero")
  else ok(x / y)
  end
end

# Lambda with multiple parameters
let add = fn(x, y) -> x + y end
```

## Expressions

### Literals
```cure
# Numbers
42                     # Integer
3.14                   # Float
-5                     # Negative integer

# Strings
"Hello, World!"        # Simple string
"Line 1\nLine 2"       # String with escape sequences
"Quote: \"text\""      # String with escaped quotes

# Booleans
true
false

# Atoms
:ok
:error  
:increment
:atom_name

# Lists
[]                     # Empty list
[1, 2, 3]             # List of integers
["a", "b", "c"]       # List of strings

# Tuples
{}                     # Empty tuple (Unit)
{42}                   # Single element tuple
{1, "hello", true}     # Multi-element tuple
{:ok, "success"}       # Tagged tuple
```

### Binary Operations
```cure
# Arithmetic
x + y                  # Addition
x - y                  # Subtraction  
x * y                  # Multiplication
x / y                  # Division

# Comparison
x == y                 # Equality
x != y                 # Inequality
x < y                  # Less than
x > y                  # Greater than
x <= y                 # Less than or equal
x >= y                 # Greater than or equal

# String operations
str1 ++ str2           # String concatenation

# List operations
x :: xs                # Cons (prepend to list)

# Pipe operator
value |> function      # Function composition
```

### Unary Operations
```cure
-x                     # Negation
not(condition)         # Logical negation
```

### Conditional Expressions
```cure
# If-then-else
if condition then
  expression1
else  
  expression2
end

# Nested conditionals
if x > 0 then "positive"
else if x < 0 then "negative"
else "zero"
end
```

### Let Expressions
```cure
# Simple binding
let x = 42

# Multiple bindings
let x = calculate_x()
let y = calculate_y(x)
let result = x + y

# Binding with pattern matching
let [head | tail] = some_list
```

### Function Calls
```cure
# Simple function call
add(5, 3)

# Method-style calls with pipe operator
numbers
  |> filter(fn(x) -> x > 0 end)  
  |> map(fn(x) -> x * 2 end)
  |> fold(0, fn(x, acc) -> acc + x end)

# Module-qualified calls ✅ **WORKING**
Std.List.map(list, function)
print("Hello")  # From imported Std module
```

## Pattern Matching

### Basic Pattern Matching
```cure
match expression do
  pattern1 -> result1
  pattern2 -> result2
  _ -> default_result  # Wildcard pattern
end
```

### List Pattern Matching
```cure
match list do
  [] -> "empty list"
  [x] -> "single element: " ++ show(x)
  [x, y] -> "two elements: " ++ show(x) ++ " and " ++ show(y)
  [head | tail] -> "head: " ++ show(head) ++ ", tail length: " ++ show(length(tail))
end
```

### Pattern Matching with Guards
```cure
match n do
  x when x < 0 -> "negative: " ++ show(x)
  x when x == 0 -> "zero"
  x when x > 0 and x <= 10 -> "small positive: " ++ show(x)
  x when x > 100 -> "large positive: " ++ show(x)
  x -> "other: " ++ show(x)
end
```

### Record Pattern Matching
```cure
record Person do
  name: String
  age: Int
  email: String
end

match person do
  Person{name: "Alice", age: age} ->
    "Special greeting for Alice, age " ++ show(age)
  Person{name: name, age: age} when age >= 18 ->
    "Hello, adult " ++ name ++ "!"
  Person{name: name} ->
    "Hello, young " ++ name ++ "!"
end
```

### Result and Option Pattern Matching
```cure
# Result handling
match result do
  Ok(value) when value > 100 -> "Success with large value: " ++ show(value)
  Ok(value) -> "Success: " ++ show(value)
  Error(msg) -> "Failed: " ++ msg
end

# Option handling
match option do
  Some(value) -> "Found: " ++ show(value)
  None -> "Not found"
end
```

### Tuple Pattern Matching
```cure
match coordinates do
  {0.0, 0.0} -> "Origin point"
  {x, 0.0} -> "On X-axis at " ++ show(x)
  {0.0, y} -> "On Y-axis at " ++ show(y)
  {x, y} when x == y -> "Diagonal point"
  {x, y} -> "Point: (" ++ show(x) ++ ", " ++ show(y) ++ ")"
end
```

### Nested Pattern Matching
```cure
match nested_result do
  Ok(Some(value)) when value > 0 -> "Positive value: " ++ show(value)
  Ok(Some(value)) -> "Non-positive value: " ++ show(value)
  Ok(None) -> "Success but no value"
  Error(msg) -> "Error: " ++ msg
end
```

### Case Expressions (Alternative Syntax)
```cure
case expression of
  pattern1 -> result1
  pattern2 -> result2
  _ -> default_result
end
```

## Dependent Types

### Length-Indexed Types ✅ **WORKING**
```cure
# Vector operations with compile-time safety
def make_vec3(x: Float, y: Float, z: Float): Vector(Float, 3) =
  [x, y, z]  # Type system guarantees exactly 3 elements

def dot_product(v1: Vector(Float, n), v2: Vector(Float, n)): Float =
  # Type system guarantees v1 and v2 have identical length
  zip_with(v1, v2, fn(x, y) -> x * y end)
  |> fold(0.0, fn(x, acc) -> acc + x end)

def vector_add(v1: Vector(Float, n), v2: Vector(Float, n)): Vector(Float, n) =
  # Type system ensures result has the same length as inputs
  zip_with(v1, v2, fn(x, y) -> x + y end)
```

### Matrix Operations with Dimension Checking
```cure
record Matrix(rows: Nat, cols: Nat, T) do
  data: Vector(Vector(T, cols), rows)
end

def matrix_multiply(
  a: Matrix(m, n, T), 
  b: Matrix(n, p, T)
): Matrix(m, p, T) = 
  # Implementation ensures dimensions match at compile time
  ...
```

### Refinement Types
```cure
# Types with logical constraints
type NonEmptyList(T) = List(T, n) when n > 0
type PositiveInt = {x: Int | x > 0}
type NonNegativeFloat = {x: Float | x >= 0.0}

def head(list: NonEmptyList(T)): T =
  match list do
    [x|_] -> x
    # No need for empty case - type system guarantees non-empty
  end
```

### Function-Dependent Types
```cure
# Return type depends on input parameter
def replicate(n: Nat, x: T): List(T, n) = 
  if n == 0 then [] else x :: replicate(n-1, x)

# List concatenation with length preservation
def append(xs: List(T, n), ys: List(T, m)): List(T, n + m) =
  match xs do
    [] -> ys
    [x|rest] -> x :: append(rest, ys)
  end
```

## Finite State Machines

### Basic FSM Definition
```cure
fsm TrafficLight do
  states: [Red, Yellow, Green]
  initial: Red
  
  state Red do
    event(:timer) -> Green
    event(:emergency) -> Red  # Self-transition
  end
  
  state Yellow do
    event(:timer) -> Red
  end
  
  state Green do
    event(:timer) -> Yellow
    event(:emergency) -> Red
  end
end
```

### FSM with State Data and Guards
```cure
fsm Counter(max_value: Int) do
  states: [Zero, Counting(n: Int) where 0 < n <= max_value]
  initial: Zero
  data: {current: Int}
  
  state Zero do
    event(:increment) -> 
      data.current := 1
      Counting(1)
  end
  
  state Counting(n) do
    event(:increment) when n < max_value ->
      data.current := n + 1
      Counting(n + 1)
    event(:decrement) when n > 1 ->
      data.current := n - 1  
      Counting(n - 1)
    event(:reset) ->
      data.current := 0
      Zero
  end
end
```

### FSM Operations
```cure
# Spawn FSM instances
let light = fsm_spawn(TrafficLight)
let counter = fsm_spawn(Counter, 100)

# Send events
fsm_send(light, :timer)
fsm_send(counter, :increment)

# Query FSM state
let current_state = fsm_state(light)
let is_running = fsm_is_alive(counter)
```

### FSM Safety Properties
```cure
fsm TrafficLightWithSafety do
  states: [Red, Yellow, Green]
  initial: Red
  
  # Safety properties for verification
  property safety_never_conflicting: 
    always (not (red and green))
  
  property liveness_eventually_green: 
    always (red -> eventually green)
  
  # State definitions...
end
```

## Process Definitions

### Basic Process
```cure
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
```

### Process Communication
```cure
# Spawn processes
let counter = spawn(counter_server, [0])

# Send messages
send(counter, {:increment})
send(counter, {:get, self()})

# Receive messages
receive do
  {:count, value} -> print("Count: " ++ show(value))
  timeout(5000) -> print("Timeout!")
end
```

## Standard Library Integration

### Working Import System ✅
```cure
module Example do
  # Import core types and functions
  import Std [Result, Option, print/1, show/1]
  
  # Import list operations
  import Std.List [map/2, filter/2, fold/3]
  
  def demo(): Unit =
    let numbers = [1, 2, 3, 4, 5]
    let doubled = map(numbers, fn(x) -> x * 2 end)
    let sum = fold(doubled, 0, fn(x, acc) -> acc + x end)
    print("Sum: " ++ show(sum))  # Output: "Sum: 30"
end
```

### Core Standard Library Functions ✅ **VERIFIED**
```cure
# Output functions (runtime verified)
print/1      # Print values to console with proper formatting
show/1       # Convert values to string representation

# List operations (runtime verified)
map/2        # Transform list elements
fold/3       # Reduce list with accumulator  
zip_with/3   # Combine two lists
head/1       # Get first element of list
tail/1       # Get list without first element
cons/2       # Prepend element
append/2     # Join two lists
length/1     # Get list length
filter/2     # Filter list elements
contains/2   # Check if list contains element
```

### Result and Option Types
```cure
# Chainable error handling
result = safe_divide(x, y)
  |> map_ok(fn(val) -> val * 2 end)
  |> and_then(fn(doubled) -> safe_sqrt(doubled) end)

match result do
  Ok(final_value) -> print("Success: " ++ show(final_value))
  Error(msg) -> print("Error: " ++ msg)
end
```

## Grammar Reference

### EBNF Grammar
```ebnf
# Top-level program structure
program ::= module_def | item*

module_def ::= 'module' IDENTIFIER 'do' export_list? item* 'end'

export_list ::= 'export' '[' export_item (',' export_item)* ']'
export_item ::= IDENTIFIER ('/' INTEGER)?

# Top-level items
item ::= function_def | type_def | record_def | fsm_def 
       | process_def | import_def | let_binding

# Function definitions
function_def ::= ('def' | 'defp') IDENTIFIER '(' param_list? ')' type_annotation? constraint? '=' expr

param_list ::= param (',' param)*
param ::= IDENTIFIER ':' type

type_annotation ::= '->' type | ':' type
constraint ::= 'when' expr

# Import definitions
import_def ::= 'import' IDENTIFIER import_list?
import_list ::= '[' import_item (',' import_item)* ']'
import_item ::= IDENTIFIER ('/' INTEGER)?

# Types
type ::= primitive_type | compound_type | dependent_type | function_type | union_type

primitive_type ::= 'Int' | 'Float' | 'String' | 'Bool' | 'Atom' | 'Binary' | 'Unit' | 'Nat' | 'Pos' | 'Pid'

compound_type ::= IDENTIFIER type_args?
                | '[' type ']'  # List type
                | '{' type (',' type)* '}'  # Tuple type

dependent_type ::= IDENTIFIER '(' type_arg (',' type_arg)* ')'
type_arg ::= type | expr

# Expressions  
expr ::= literal | identifier | function_call | match_expr | if_expr 
       | let_expr | binary_op | unary_op | lambda_expr | list_expr | tuple_expr

literal ::= INTEGER | FLOAT | STRING | ATOM | BOOLEAN

# Pattern matching
match_expr ::= 'match' expr 'do' match_clause* 'end'
match_clause ::= pattern guard? '->' expr
pattern ::= literal | identifier | list_pattern | tuple_pattern | record_pattern | wildcard
guard ::= 'when' expr

# FSM definitions
fsm_def ::= 'fsm' IDENTIFIER 'do' fsm_body 'end'
fsm_body ::= fsm_clause*
fsm_clause ::= 'states' ':' '[' state_list ']'
            | 'initial' ':' IDENTIFIER
            | state_def

state_def ::= 'state' IDENTIFIER 'do' transition* 'end'
transition ::= 'event' '(' pattern ')' '->' IDENTIFIER
```

### Lexical Tokens
```cure
IDENTIFIER ::= [a-zA-Z_][a-zA-Z0-9_]*
INTEGER ::= [0-9]+
FLOAT ::= [0-9]+ '.' [0-9]+
STRING ::= '"' ([^"\\] | '\\' .)* '"'
ATOM ::= ':' IDENTIFIER | ':"' ([^"\\] | '\\' .)* '"'
BOOLEAN ::= 'true' | 'false'
```

## Examples and Usage Patterns

### Complete Working Example ✅
```cure
module DependentTypes do
  export [demo_all/0]
  import Std [List, Result, print/1, show/1]
  
  # Length-indexed vectors with compile-time safety
  def make_vec3(x: Float, y: Float, z: Float): Vector(Float, 3) =
    [x, y, z]
  
  def dot_product(v1: Vector(Float, n), v2: Vector(Float, n)): Float =
    zip_with(v1, v2, fn(x, y) -> x * y end)
    |> fold(0.0, fn(x, acc) -> acc + x end)
  
  def demo_all(): Unit =
    let v1 = make_vec3(1.0, 2.0, 3.0)
    let v2 = make_vec3(4.0, 5.0, 6.0)
    let result = dot_product(v1, v2)  # 32.0
    print("Dot product: " ++ show(result))
end

# Successfully compiles and runs!
# Output: Dot product: 32.0
```

---

This syntax reference covers all implemented features of the Cure programming language with working examples and comprehensive documentation of the grammar, type system, and standard library integration.