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

### Module System

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

# Import
import Math
import List [map/2, filter/2]

# Usage
let result = Math.add(5, 3)
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

### Dependent Types Examples

```cure
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
program ::= module_def | item*

module_def ::= 'module' IDENTIFIER 'do' export_list? item* 'end'

export_list ::= 'export' '[' export_item (',' export_item)* ']'

item ::= function_def | type_def | fsm_def | process_def | import_def

function_def ::= 'def' IDENTIFIER '(' param_list? ')' type_annotation? constraint? '=' expr

param_list ::= param (',' param)*
param ::= IDENTIFIER ':' type

type_annotation ::= '->' type | ':' type

constraint ::= 'when' expr

type ::= primitive_type | dependent_type | function_type | union_type

expr ::= literal | identifier | function_call | match_expr | if_expr | ...

# ... more grammar rules
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
