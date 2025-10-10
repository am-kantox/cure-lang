# Cure Language Specification

## Overview

Cure is a dependently-typed functional programming language targeting the BEAM virtual machine. It combines the actor model and fault-tolerance of Erlang/Elixir with a powerful dependent type system and built-in finite state machines.

## Core Principles

1. **Dependent Types**: Types can depend on values, enabling precise specifications
2. **Process-Oriented**: Built on the actor model with lightweight processes
3. **Fault Tolerance**: "Let it crash" philosophy with supervision trees
4. **Immutability**: All data structures are immutable by default
5. **Pattern Matching**: Comprehensive pattern matching with dependent constraints
6. **FSM Integration**: Finite state machines as first-class constructs

## Syntax Overview

### Basic Types

```cure
# Primitive types
Int                    # Arbitrary precision integers
Float                  # Double precision floats
Atom                   # Interned symbols (like Elixir atoms)
Bool                   # true | false
String                 # UTF-8 strings
Binary                 # Byte sequences
Unit                   # Unit type for functions with no meaningful return

# Dependent types
Nat                    # Natural numbers (Int >= 0)
Pos                    # Positive integers (Int > 0)
Vector(T, n: Nat)      # Fixed-length vector
List(T, n: Nat)        # List with known length
Range(min: Int, max: Int)  # Integer range type
```

### Function Definitions

```cure
# Simple function
def add(x: Int, y: Int): Int = x + y

# Function with dependent types
def replicate(n: Nat, x: T): List(T, n) = 
  if n == 0 then [] else x :: replicate(n-1, x)

# Pattern matching function
def length(list: List(T)) -> Nat =
  match list do
    [] -> 0
    [_|tail] -> 1 + length(tail)
  end

# Function with constraints
def safe_divide(x: Int, y: Int) -> Int when y != 0 = x / y

# Function with Unit return type
def print_message(msg: String): Unit =
  print("Message: " ++ msg)
  ok
```

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

### Finite State Machines

```cure
# FSM definition
fsm tcp_connection do
  # State declarations
  states: [Closed, Listen, SynSent, SynReceived, Established, FinWait1, FinWait2, Closing, TimeWait, CloseWait, LastAck]
  
  # Initial state
  initial: Closed
  
  # State definitions with transitions
  state Closed do
    event(:listen) -> Listen
    event(:connect) -> SynSent
  end
  
  state Listen do
    event(:syn_received) -> SynReceived
    event(:close) -> Closed
  end
  
  state SynSent do
    event(:syn_ack_received) -> Established
    event(:syn_received) -> SynReceived
    event(:close) -> Closed
  end
  
  state Established do
    event(:fin_received) -> CloseWait
    event(:close) -> FinWait1
    # Can handle data transfer events
    event({:data, payload: Binary}) -> Established
  end
  
  # ... more states
end

# Using FSM
let conn = fsm_spawn(tcp_connection)
fsm_send(conn, :listen)
```

### Module System ✅ **WORKING!**

```cure
# Module definition
module Math do
  # Export declarations
  export [add/2, multiply/2, factorial/1]
  
  def add(x: Int, y: Int): Int = x + y
  
  def multiply(x: Int, y: Int): Int = x * y
  
  def factorial(n: Nat): Pos =
    if n == 0 then 1 else n * factorial(n - 1)
    
  # Private function
  defp helper_func(x) = x * 2
end

# 🚀 WORKING Import System!
import Math
import Std [List, Result]         # Standard library import
import List [map/2, filter/2]     # Selective imports with arity

# Usage - all work correctly!
let result = add(5, 3)            # Imported function
let doubled = map([1,2,3], fn(x) -> x * 2 end)  # From Std
print("Result: " ++ show(result)) # print/1 and show/1 from Std
```

### 🚀 Standard Library (NEW!)

Cure now includes a working standard library with essential functions:

```cure
# The Std module provides:

# Output functions
print/1      # Print values to console with formatting
show/1       # Convert values to string representation

# List operations
map/2        # Transform list elements: map([1,2,3], fn(x) -> x*2 end)
fold/3       # Reduce list with accumulator: fold([1,2,3], 0, fn(x,acc) -> acc+x end)
zip_with/3   # Combine two lists: zip_with([1,2], [3,4], fn(x,y) -> x+y end)
head/1       # Get first element
tail/1       # Get list without first element
cons/2       # Prepend element: cons(1, [2,3]) == [1,2,3]
append/2     # Join two lists
length/1     # Get list length

# Example usage:
module Example do
  import Std [List, Result]
  
  def demo(): Unit =
    let numbers = [1, 2, 3, 4, 5]
    let doubled = map(numbers, fn(x) -> x * 2 end)
    let sum = fold(doubled, 0, fn(x, acc) -> acc + x end)
    print("Sum of doubled numbers: " ++ show(sum))  # Output: 30
end
```

### Lambda Expressions and Pipe Operators

```cure
# Lambda expressions
let double = fn(x) -> x * 2 end
let add = fn(x, y) -> x + y end

# Multi-line lambda
let safe_divide = fn(x, y) ->
  if y == 0 then error("Division by zero")
  else ok(x / y)
  end
end

# Pipe operator for function composition
let result = input
  |> validate_input()
  |> process_data()
  |> format_output()

# Lambda with pipe
let processed = numbers
  |> filter(fn(x) -> x > 0 end)
  |> map(fn(x) -> x * 2 end)
```

### Data Types and Records

```cure
# Record definition
record Person do
  name: String
  age: Nat
  email: String
end

# Creating records
let person = Person{name: "Alice", age: 30, email: "alice@example.com"}

# Pattern matching on records
def greet(person: Person): String =
  match person do
    Person{name: name, age: age} when age >= 18 ->
      "Hello, adult #{name}!"
    Person{name: name} ->
      "Hello, young #{name}!"
  end

# Union types
type Result(T, E) = Ok(T) | Error(E)

type Maybe(T) = Some(T) | None
```

### 🎆 Dependent Types Examples ✅ **WORKING!**

```cure
# 🚀 WORKING: Length-indexed vectors with compile-time safety
module VectorOps do
  import Std [List, Result]
  
  # Vector type parameterized by length and element type
  def make_vec3(x: Float, y: Float, z: Float): Vector(Float, 3) =
    [x, y, z]
  
  # Safe vector operations - length checked at compile time
  def dot_product(v1: Vector(Float, n), v2: Vector(Float, n)): Float =
    # Type system guarantees v1 and v2 have the same length
    zip_with(v1, v2, fn(x, y) -> x * y end)
    |> fold(0.0, fn(x, acc) -> acc + x end)
  
  def vector_add(v1: Vector(Float, n), v2: Vector(Float, n)): Vector(Float, n) =
    # Type system ensures result has the same length as inputs
    zip_with(v1, v2, fn(x, y) -> x + y end)
end

# 🚀 WORKING: Safe operations with dependent constraints
def safe_head(list: List(T, n)) -> T when n > 0 =
  # Type system guarantees list is non-empty
  match list do
    [x | _] -> x
    # No need for empty case - type system prevents it
  end

def safe_tail(list: List(T, n)) -> List(T, n-1) when n > 0 =
  match list do
    [_ | tail] -> tail
    # No need for empty case - type system prevents it
  end

# Successfully compiles and runs!
# Example output:
# Dot product: 32.0
# Vector sum: [5.0, 7.0, 9.0]

# Length-indexed lists
def append(xs: List(T, n), ys: List(T, m)): List(T, n + m) =
  match xs do
    [] -> ys
    [x|rest] -> x :: append(rest, ys)
  end

# Matrix operations with dimension checking
record Matrix(rows: Nat, cols: Nat, T) do
  data: Vector(Vector(T, cols), rows)
end

def matrix_multiply(
  a: Matrix(m, n, T), 
  b: Matrix(n, p, T)
): Matrix(m, p, T) = 
  # Implementation ensures dimensions match at compile time
  ...

# Refinement types
type NonEmptyList(T) = List(T, n) when n > 0

def head(list: NonEmptyList(T)): T =
  match list do
    [x|_] -> x
    # No need for empty case - type system guarantees non-empty
  end
```

## Grammar (EBNF-like)

```ebnf
# Top-level program structure
program ::= module_def | item*

module_def ::= 'module' IDENTIFIER 'do' export_list? item* 'end'

export_list ::= 'export' '[' export_item (',' export_item)* ']'
export_item ::= IDENTIFIER '/' INTEGER

# Top-level items
item ::= function_def | type_def | record_def | fsm_def | process_def 
       | import_def | let_binding

# Function definitions
function_def ::= ('def' | 'defp') IDENTIFIER '(' param_list? ')' type_annotation? constraint? '=' expr

param_list ::= param (',' param)*
param ::= IDENTIFIER ':' type

type_annotation ::= '->' type | ':' type

constraint ::= 'when' expr

# Type definitions
type_def ::= 'type' IDENTIFIER type_params? '=' type_expr
record_def ::= 'record' IDENTIFIER type_params? 'do' field_list 'end'

type_params ::= '(' type_param (',' type_param)* ')'
type_param ::= IDENTIFIER | IDENTIFIER ':' type

field_list ::= field*
field ::= IDENTIFIER ':' type

# FSM definitions
fsm_def ::= 'fsm' IDENTIFIER 'do' fsm_body 'end'
fsm_body ::= fsm_clause*
fsm_clause ::= 'states' ':' '[' state_list ']'
            | 'initial' ':' IDENTIFIER
            | state_def

state_list ::= IDENTIFIER (',' IDENTIFIER)*
state_def ::= 'state' IDENTIFIER 'do' transition* 'end'
transition ::= 'event' '(' pattern ')' '->' IDENTIFIER

# Process definitions
process_def ::= 'process' IDENTIFIER '(' param_list? ')' 'do' process_body 'end'
process_body ::= item* expr

# Import definitions ✅ WORKING!
import_def ::= 'import' IDENTIFIER import_list?
import_list ::= '[' import_item (',' import_item)* ']'
import_item ::= IDENTIFIER | IDENTIFIER '/' INTEGER  # Function name or name/arity

# Let bindings
let_binding ::= 'let' IDENTIFIER '=' expr

# Types
type ::= primitive_type | compound_type | dependent_type | function_type 
       | union_type | refinement_type

primitive_type ::= 'Int' | 'Float' | 'Atom' | 'Bool' | 'String' | 'Binary'
                 | 'Nat' | 'Pos' | 'Pid'

compound_type ::= IDENTIFIER type_args?
                | '[' type ']'  # List type
                | '{' type (',' type)* '}'  # Tuple type

dependent_type ::= IDENTIFIER '(' type_arg (',' type_arg)* ')'
type_arg ::= type | expr

function_type ::= '(' param_list ')' '->' type

union_type ::= type ('|' type)+

refinement_type ::= type 'when' expr
                  | '{' IDENTIFIER ':' type '|' expr '}'

# Expressions
expr ::= literal | identifier | function_call | match_expr | if_expr 
       | case_expr | receive_expr | record_expr | list_expr | tuple_expr 
       | binary_op | unary_op | lambda_expr | spawn_expr | send_expr | fsm_expr

literal ::= INTEGER | FLOAT | STRING | ATOM | BOOLEAN

identifier ::= IDENTIFIER | qualified_identifier
qualified_identifier ::= IDENTIFIER '.' IDENTIFIER

function_call ::= expr '(' arg_list? ')'
arg_list ::= expr (',' expr)*

# Pattern matching
match_expr ::= 'match' expr 'do' match_clause* 'end'
match_clause ::= pattern guard? '->' expr
pattern ::= literal | identifier | constructor_pattern | list_pattern 
          | tuple_pattern | record_pattern | wildcard
constructor_pattern ::= IDENTIFIER pattern_args?
pattern_args ::= '(' pattern (',' pattern)* ')'
list_pattern ::= '[' ']' | '[' pattern (',' pattern)* ']' 
               | '[' pattern '|' pattern ']'
tuple_pattern ::= '{' pattern (',' pattern)* '}'
record_pattern ::= IDENTIFIER '{' field_pattern (',' field_pattern)* '}'
field_pattern ::= IDENTIFIER ':' pattern | IDENTIFIER
wildcard ::= '_'
guard ::= 'when' expr

# Conditional expressions
if_expr ::= 'if' expr 'then' expr 'else' expr
case_expr ::= 'case' expr 'of' case_clause* 'end'
case_clause ::= pattern guard? '->' expr

# Process communication
receive_expr ::= 'receive' 'do' receive_clause* 'end'
receive_clause ::= pattern guard? '->' expr

spawn_expr ::= 'spawn' '(' IDENTIFIER ',' '[' arg_list? ']' ')'
send_expr ::= 'send' '(' expr ',' expr ')'

# FSM operations
fsm_expr ::= 'fsm_spawn' '(' IDENTIFIER ')'
           | 'fsm_send' '(' expr ',' expr ')'

# Data structures
record_expr ::= IDENTIFIER '{' field_assign (',' field_assign)* '}'
field_assign ::= IDENTIFIER ':' expr

list_expr ::= '[' ']' | '[' expr (',' expr)* ']'

tuple_expr ::= '{' expr (',' expr)* '}'

# Operators
binary_op ::= expr binary_operator expr
unary_op ::= unary_operator expr

binary_operator ::= '+' | '-' | '*' | '/' | '==' | '!=' | '<' | '>' 
                  | '<=' | '>=' | '&&' | '||' | '::' | '++' | '|>'
unary_operator ::= '-' | '!'

# Lambda expressions
lambda_expr ::= 'fn' '(' param_list? ')' '->' expr ('end')?
              | 'fn' '(' param_list? ')' '->' expr_block 'end'

expr_block ::= expr+

# String interpolation
string_interpolation ::= '"' string_part* '"'
string_part ::= STRING_CHARS | '#{' expr '}'

# Lexical tokens
IDENTIFIER ::= [a-zA-Z_][a-zA-Z0-9_]*
INTEGER ::= [0-9]+
FLOAT ::= [0-9]+ '.' [0-9]+
STRING ::= '"' ([^"\\] | '\\' .)* '"'
ATOM ::= ':' IDENTIFIER | ':"' ([^"\\] | '\\' .)* '"'
BOOLEAN ::= 'true' | 'false'
COMMENT ::= '#' [^\n]*
WHITESPACE ::= [ \t\n\r]+
```

## Type System

The type system is based on dependent types with the following features:

1. **Pi Types**: Dependent function types `(x: A) -> B(x)`
2. **Sigma Types**: Dependent pair types `{x: A, B(x)}`
3. **Refinement Types**: Types with predicates `{x: T | P(x)}`
4. **Indexed Types**: Types parameterized by values
5. **Linear Types**: Resource-aware typing (future feature)

## Compilation Model

1. **Source** → **Tokens** (Lexer)
2. **Tokens** → **AST** (Parser) 
3. **AST** → **Typed AST** (Type Checker)
4. **Typed AST** → **Core IR** (Desugaring)
5. **Core IR** → **BEAM Bytecode** (Code Generator)

## Runtime Integration

- **Processes**: Map to BEAM processes
- **FSMs**: Compile to gen_statem behaviors
- **Pattern Matching**: Use BEAM's efficient matching
- **Tail Calls**: Leverage BEAM's tail call optimization
- **Hot Code Loading**: Support BEAM's code upgrade mechanisms
- **Distribution**: Transparent distribution across nodes

## Future Extensions

- **Effect System**: Track computational effects
- **Linear Types**: Resource management
- **Gradual Typing**: Interop with dynamic Erlang/Elixir
- **Proof Assistants**: Integration with formal verification
- **Macros**: Compile-time code generation
