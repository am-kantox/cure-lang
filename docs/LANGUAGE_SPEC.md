# Cure Language Specification

## Syntax Overview

Cure is an indentation-structured language. Blocks are delimited by
indentation level, not by keywords like `do`/`end` or braces.

### Keywords

`fn`, `mod`, `rec`, `fsm`, `proto`, `impl`, `type`, `let`, `if`, `then`,
`else`, `elif`, `match`, `when`, `where`, `local`, `use`, `return`, `throw`,
`try`, `catch`, `finally`, `for`, `in`, `true`, `false`, `nil`,
`and`, `or`, `not`

### Operators (by precedence, low to high)

- `|>` -- pipe (left-assoc)
- `or` -- boolean or (left-assoc)
- `and` -- boolean and (left-assoc)
- `==`, `!=`, `<`, `>`, `<=`, `>=` -- comparison (non-assoc)
- `..`, `..=` -- range (non-assoc)
- `<>` -- string concat (right-assoc)
- `+`, `-` -- additive (left-assoc)
- `*`, `/`, `%` -- multiplicative (left-assoc)
- `-`, `not` -- unary prefix
- `.` -- field access (left-assoc)

### Literals

- Integers: `42`, `0xFF`, `0b1010`
- Floats: `3.14`
- Strings: `"hello"`, `"hello #{name}"`
- Booleans: `true`, `false`
- Atoms: `:ok`, `:error`
- Nil: `nil`
- Chars: `'a'`
- Lists: `[1, 2, 3]`, `[h | t]`
- Tuples: `%[a, b]`
- Maps: `%{key: value}`

## Modules

```cure
mod MyApp.Math
  fn add(a: Int, b: Int) -> Int = a + b
  local fn helper() -> Int = 42
```

All functions are public by default. Use `local fn` for private.

## Functions

### Single-expression body

```cure
fn add(a: Int, b: Int) -> Int = a + b
```

### Multi-expression body (indented block)

```cure
fn compute(x: Int) -> Int =
  let y = x * 2
  let z = y + 1
  z
```

### Multi-clause (pattern matching on arguments)

```cure
fn factorial(n: Int) -> Int
  | 0 -> 1
  | n -> n * factorial(n - 1)
```

### Guards

```cure
fn abs(x: Int) -> Int when x >= 0 = x

fn classify(x: Int) -> String
  | x when x > 0 -> "positive"
  | x when x < 0 -> "negative"
  | _ -> "zero"
```

### FFI (Foreign Function Interface)

```cure
@extern(:erlang, :abs, 1)
fn abs(x: Int) -> Int
```

## Types

### Primitive types

`Int`, `Float`, `String`, `Bool`, `Atom`, `Pid`, `Char`

### Composite types

- `List(T)` -- linked list
- `Map(K, V)` -- hash map
- `%[A, B]` -- tuple
- `A -> B` -- function type

### ADT (sum types)

```cure
type Option(T) = Some(T) | None
type Result(T, E) = Ok(T) | Error(E)
```

### Refinement types

```cure
type NonZero = {x: Int | x != 0}
type Positive = {x: Int | x > 0}
type Percentage = {p: Int | p >= 0 and p <= 100}
```

Refinement type subtyping is verified at compile time using Z3.

## Protocols

```cure
proto Show(T)
  fn show(x: T) -> String

impl Show for Int
  fn show(x: Int) -> String = Std.String.from_int(x)
```

Protocol dispatch is compiled to guard-based multi-clause functions.

## FSMs (Finite State Machines)

```cure
fsm TrafficLight
  Red    --timer-->     Green
  Green  --timer-->     Yellow
  Yellow --timer-->     Red
  *      --emergency--> Red
```

FSMs compile to `gen_statem` BEAM modules. The compiler verifies
reachability and deadlock freedom at compile time.

## Pattern Matching

```cure
match x
  Ok(v) -> v
  Error(e) -> default

match list
  [] -> "empty"
  [h | t] -> "non-empty"
```

The compiler checks pattern exhaustiveness and warns about missing cases.

## Control Flow

### If/else

```cure
if x > 0 then "positive" else "non-positive"
```

### Let bindings

```cure
let x = 42
let y = x * 2
```

### Pipe operator

```cure
5 |> double |> add(1)
# desugars to: add(double(5), 1)
```
