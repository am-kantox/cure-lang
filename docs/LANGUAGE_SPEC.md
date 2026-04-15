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

## Records

Records are named, typed product types. They compile to BEAM maps with a
`__struct__` discriminator key, giving them nominal identity at runtime.

### Definition

```cure
rec Point
  x: Int
  y: Int

rec Person
  name: String
  age: Int

rec Rectangle
  origin: Point
  width: Int
  height: Int
```

Type parameters are supported for generic records:

```cure
rec Pair(A, B)
  first: A
  second: B
```

Type parameters are erased at runtime but are tracked by the type checker.

### Construction

Use `TypeName{field: expr, ...}` to build a record value:

```cure
fn make_point(x: Int, y: Int) -> Point = Point{x: x, y: y}
fn origin() -> Point = Point{x: 0, y: 0}
fn make_person(name: String, age: Int) -> Person =
  Person{name: name, age: age}
```

### Field access

Use dot notation `record.field`, which compiles to `maps:get(field, map)`:

```cure
fn x_coord(p: Point) -> Int = p.x
fn area(r: Rectangle) -> Int = r.width * r.height
fn rect_origin_x(r: Rectangle) -> Int = r.origin.x  # nested access
```

### Record update

Produce a modified copy of a record with `TypeName{base | field: val, ...}`.
Only the listed fields change; all others are copied from `base`:

```cure
fn set_x(p: Point, new_x: Int) -> Point = Point{p | x: new_x}
fn birthday(p: Person) -> Person = Person{p | age: p.age + 1}
fn translate(p: Point, dx: Int, dy: Int) -> Point =
  Point{p | x: p.x + dx, y: p.y + dy}
fn rename(p: Person, new_name: String) -> Person =
  Person{p | name: new_name}
```

Multiple fields can be overridden in one expression:

```cure
fn move(p: Point, nx: Int, ny: Int) -> Point = Point{p | x: nx, y: ny}
```

The type name before `{` is required and must match the type of the base
expression. The compiler verifies override field types against the declared
schema.

### Runtime representation

Records compile to BEAM maps:

```
Point{x: 3, y: 4}  ->  %{__struct__: :point, x: 3, y: 4}
```

Record construction uses `map_field_assoc` (`:=>`). Record update uses
`map_field_exact` (`:=`) which requires the keys to already exist, giving
a `bad_key` error at runtime if the base value has an incompatible shape.

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
