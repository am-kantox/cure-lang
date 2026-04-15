%{
  title: "Language Guide",
  description: "Complete syntax reference for the Cure programming language.",
  order: 2
}
---
Cure is an indentation-structured, expression-oriented language that compiles to BEAM bytecode. Blocks are delimited by indentation level -- no `do`/`end`, no braces. The last expression in a block is its value.

## Modules

Every Cure source file contains one module. The module name follows Elixir/Erlang dot-separated conventions:

```cure
mod MyApp.Math
  fn add(a: Int, b: Int) -> Int = a + b
  fn sub(a: Int, b: Int) -> Int = a - b
```

All functions inside a module are public by default. Use `local fn` for private functions:

```cure
mod MyApp.Internal
  fn public_api(x: Int) -> Int = helper(x) + 1

  local fn helper(x: Int) -> Int = x * 2
```

## Functions

### Single-expression body

When the body is a single expression, write it after `=` on the same line:

```cure
fn add(a: Int, b: Int) -> Int = a + b
fn greet(name: String) -> String = "Hello, " <> name <> "!"
fn identity(x: T) -> T = x
```

### Multi-expression body

For multiple expressions, put `=` at the end of the signature line, then indent the body:

```cure
fn compute(x: Int) -> Int =
  let y = x * 2
  let z = y + 1
  z
```

The last expression (`z`) is the return value.

### Multi-clause functions

Pattern match on arguments using `|` clauses:

```cure
fn factorial(n: Int) -> Int
  | 0 -> 1
  | n -> n * factorial(n - 1)

fn describe(x: Int) -> String
  | 0 -> "zero"
  | 1 -> "one"
  | _ -> "other"

fn fibonacci(n: Int) -> Int
  | 0 -> 0
  | 1 -> 1
  | n -> fibonacci(n - 1) + fibonacci(n - 2)
```

### Guards

Guards restrict when a function clause or pattern applies. Use `when` after the parameter list or after the pattern:

```cure
fn abs(x: Int) -> Int when x >= 0 = x

fn classify(x: Int) -> String
  | x when x > 0 -> "positive"
  | x when x < 0 -> "negative"
  | _ -> "zero"
```

Guards can use comparison operators (`>`, `<`, `>=`, `<=`, `==`, `!=`), boolean operators (`and`, `or`, `not`), and arithmetic.

### Effect annotations

Functions can declare their side effects after the return type using `!`:

```cure
fn read_file(path: String) -> String ! Io
fn risky(x: Int) -> Int ! Exception
fn complex(x: Int) -> Int ! Io, Exception
```

Effect kinds: `Io`, `State`, `Exception`, `Spawn`, `Extern`. When no `!` annotation is present, effects are inferred from the body.

### Type annotations

Every parameter must have a type annotation. Return types are declared after `->`:

```cure
fn process(name: String, count: Int) -> String = name <> "!"
```

Polymorphic functions use type variables (bare capitalized identifiers):

```cure
fn identity(x: T) -> T = x
fn apply(f: A -> B, x: A) -> B = f(x)
```

## Keywords

Reserved words in Cure:

`fn`, `mod`, `rec`, `fsm`, `proto`, `impl`, `type`, `let`, `if`, `then`, `else`, `elif`, `match`, `when`, `where`, `local`, `use`, `return`, `throw`, `try`, `catch`, `finally`, `for`, `in`, `true`, `false`, `nil`, `and`, `or`, `not`

## Comments

Single-line comments start with `#`:

```cure
# This is a comment
fn add(a: Int, b: Int) -> Int = a + b  # inline comment
```

Doc comments start with `##` and are attached to the following definition. They are extracted by `cure doc` to generate HTML documentation:

```cure
## Returns the absolute value of an integer.
##
## Examples:
##   abs(-5)  # => 5
fn abs(x: Int) -> Int
  | x when x >= 0 -> x
  | x -> -x
```

## Operators

Ordered from lowest to highest precedence:

| Precedence | Operator(s) | Associativity | Description |
|---|---|---|---|
| 1 | `\|>` | left | pipe |
| 2 | `or` | left | boolean or |
| 3 | `and` | left | boolean and |
| 4 | `==` `!=` `<` `>` `<=` `>=` | non-assoc | comparison |
| 5 | `..` `..=` | non-assoc | range (exclusive, inclusive) |
| 6 | `<>` | right | string concatenation |
| 7 | `+` `-` | left | additive |
| 8 | `*` `/` `%` | left | multiplicative |
| 9 | `-` `not` | prefix | unary negation, boolean not |
| 10 | `.` | left | field access |

Examples:

```cure
# Pipe chains
5 |> double |> add(1)
# desugars to: add(double(5), 1)

# Boolean
x > 0 and x < 100 or x == -1

# String concat
"hello" <> " " <> "world"

# Range
1..10
0..=255

# Field access
point.x + point.y
```

## Literals

### Integers

```cure
42
0xFF
0b1010
1_000_000
```

### Floats

```cure
3.14
0.001
```

### Strings

Double-quoted, with interpolation via `#{}`:

```cure
"hello"
"hello #{name}"
"result: #{compute(42)}"
```

### Booleans

```cure
true
false
```

### Atoms

Prefixed with `:`:

```cure
:ok
:error
:my_atom
```

### Nil

```cure
nil
```

### Chars

Single-quoted:

```cure
'a'
'Z'
```

### Lists

```cure
[1, 2, 3]
["a", "b", "c"]
[]
```

Cons syntax for head/tail decomposition:

```cure
[h | t]
[1, 2 | rest]
```

### Tuples

Prefixed with `%`:

```cure
%[1, "hello"]
%[x, y, z]
```

### Maps

Prefixed with `%`:

```cure
%{name: "Alice", age: 30}
%{key: value}
```

## Let bindings

Introduce local variables with `let`:

```cure
fn compute(x: Int) -> Int =
  let doubled = x * 2
  let offset = 10
  doubled + offset
```

`let` bindings are immutable. Each `let` introduces a new binding; there is no reassignment.

## If / then / else

`if` is an expression and always produces a value:

```cure
fn abs(x: Int) -> Int = if x > 0 then x else 0 - x

fn sign(x: Int) -> String =
  if x > 0 then "positive"
  elif x < 0 then "negative"
  else "zero"
```

Both branches must be present when the result is used. `elif` chains multiple conditions.

## Match expressions

Pattern match on values with `match`:

```cure
fn unwrap(opt: Option(Int)) -> Int =
  match opt
    Some(v) -> v
    None() -> 0

fn describe_list(xs: List(Int)) -> String =
  match xs
    [] -> "empty"
    [h | t] -> "starts with " <> Std.String.from_int(h)

fn handle(r: Result(Int, String)) -> Int =
  match r
    Ok(v) -> v
    Error(_) -> -1
```

The compiler checks pattern exhaustiveness -- missing cases produce warnings.

## Pipe operator

The pipe operator `|>` passes the result of the left expression as the first argument to the function on the right:

```cure
fn process(xs: List(Int)) -> Int =
  xs
  |> Std.List.filter(fn(x) -> x > 0)
  |> Std.List.map(fn(x) -> x * 2)
  |> Std.List.sum()
```

## ADTs (algebraic data types)

Define sum types with `type`:

```cure
type Color = Red | Green | Blue

type Option(T) = Some(T) | None

type Result(T, E) = Ok(T) | Error(E)

type Shape = Circle(Float) | Rectangle(Float, Float) | Point
```

Use constructors as regular functions:

```cure
fn wrap(x: Int) -> Option(Int) = Some(x)
fn nothing() -> Option(Int) = None()
fn make_color() -> Color = Red()

fn safe_divide(a: Int, b: Int) -> Result(Int, String) =
  if b == 0 then Error("division by zero") else Ok(a / b)
```

Destructure ADTs with `match`:

```cure
fn unwrap_or(opt: Option(Int), default: Int) -> Int =
  match opt
    Some(v) -> v
    None() -> default
```

## Records

Records are named product types. They compile to BEAM maps and are
fully type-checked: the compiler tracks field names and types for
each `rec` definition.

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

All field types must be named. `Any` is accepted as an escape hatch but
forfeits field-level type checking for that field.

### Parameterized records

Records can take type parameters:

```cure
rec Pair(A, B)
  first: A
  second: B
```

Type parameters are erased at runtime but used by the type checker.

### Construction

Use `TypeName{field: expr, ...}` to build a record value:

```cure
fn make_point(x: Int, y: Int) -> Point = Point{x: x, y: y}
fn origin() -> Point = Point{x: 0, y: 0}
fn make_person(name: String, age: Int) -> Person =
  Person{name: name, age: age}
fn make_pair(a: Any, b: Any) -> Pair(Any, Any) = Pair{first: a, second: b}
```

Fields can appear in any order. The type checker verifies each value type
against the declared field type.

### Field access

Dot notation `record.field` looks up a field at runtime via `maps:get/2`:

```cure
fn x_coord(p: Point) -> Int = p.x
fn y_coord(p: Point) -> Int = p.y
fn person_name(p: Person) -> String = p.name
fn area(r: Rectangle) -> Int = r.width * r.height
```

Nested access chains multiple `.` operations:

```cure
fn rect_origin_x(r: Rectangle) -> Int = r.origin.x
```

### Record update

Produce a modified copy using `TypeName{base | field: val, ...}`.
Only the listed fields change; all others are preserved unchanged:

```cure
# Single-field update
fn set_x(p: Point, new_x: Int) -> Point = Point{p | x: new_x}
fn birthday(p: Person) -> Person = Person{p | age: p.age + 1}

# Multi-field update
fn translate(p: Point, dx: Int, dy: Int) -> Point =
  Point{p | x: p.x + dx, y: p.y + dy}
fn move(p: Point, nx: Int, ny: Int) -> Point =
  Point{p | x: nx, y: ny}
```

The type name before `{` is required. The base expression must have the same
record type. The compiler checks each override value against its declared
field type and returns the same named type.

Record update compiles to the BEAM map-update instruction (`Map#{key := val}`),
which copies the map and overwrites only the specified keys. The `__struct__`
field is preserved automatically.

### Records in computations

```cure
fn distance_squared(a: Point, b: Point) -> Int =
  let dx = b.x - a.x
  let dy = b.y - a.y
  dx * dx + dy * dy

fn midpoint(a: Point, b: Point) -> Point =
  Point{x: (a.x + b.x) / 2, y: (a.y + b.y) / 2}

fn older_of(a: Person, b: Person) -> Person =
  if a.age > b.age then a else b

fn greet(p: Person) -> String = "Hello, " <> p.name
```

## Protocols

Protocols provide ad-hoc polymorphism (similar to type classes or interfaces). Define with `proto`, implement with `impl`:

```cure
proto Show(T)
  fn show(x: T) -> String

impl Show for Int
  fn show(x: Int) -> String = Std.String.from_int(x)

impl Show for Bool
  fn show(x: Bool) -> String = if x then "true" else "false"

impl Show for String
  fn show(x: String) -> String = x
```

Protocol dispatch compiles to guard-based multi-clause BEAM functions.

## Imports

Import modules with `use`:

```cure
mod MyApp
  use Std.List
  use Std.Core

  fn double_all(xs: List(Int)) -> List(Int) =
    Std.List.map(xs, fn(x) -> x * 2)
```

Import multiple modules from the same namespace:

```cure
use Std.{List, Core, Math}
```

## FFI (Foreign Function Interface)

Call Erlang/OTP functions with the `@extern` attribute:

```cure
@extern(:erlang, :abs, 1)
fn abs(x: Int) -> Int

@extern(:math, :sqrt, 1)
fn sqrt(x: Float) -> Float

@extern(:erlang, :integer_to_binary, 1)
fn int_to_string(n: Int) -> String

@extern(:io, :put_chars, 1)
fn print(s: String) -> Atom
```

The three arguments are the Erlang module atom, the function atom, and the arity. The compiler generates a wrapper that delegates to the Erlang function.

## Lambdas

Anonymous functions use `fn` without a name:

```cure
fn double_all(xs: List(Int)) -> List(Int) =
  Std.List.map(xs, fn(x) -> x * 2)

fn apply_twice(f: Int -> Int, x: Int) -> Int = f(f(x))

fn make_adder(n: Int) -> Int -> Int = fn(x) -> x + n
```

Lambdas with multiple arguments:

```cure
Std.List.foldl(xs, 0, fn(x) -> fn(acc) -> acc + x)
```

Note: curried style -- each `fn` takes one argument and returns the next function.

## String interpolation

Embed expressions inside strings with `#{}`:

```cure
fn greet(name: String, age: Int) -> String =
  "Hello, #{name}! You are #{Std.String.from_int(age)} years old."
```

Any expression can appear inside `#{}`.

## Refinement types

Constrain a base type with a logical predicate:

```cure
type NonZero = {x: Int | x != 0}
type Positive = {x: Int | x > 0}
type Percentage = {p: Int | p >= 0 and p <= 100}
```

Functions can use `when` guards that are verified at call sites via Z3:

```cure
fn safe_divide(a: Int, b: Int) -> Int when b != 0 = a / b
fn positive_double(x: Int) -> Int when x > 0 = x * 2
```

See the [Type System](/pages/type-system) page for details on how refinement types and dependent type verification work.

## FSMs (Finite State Machines)

FSMs are first-class language constructs:

```cure
fsm TrafficLight
  Red    --timer-->     Green
  Green  --timer-->     Yellow
  Yellow --timer-->     Red
  *      --emergency--> Red
```

See the [Finite State Machines](/pages/finite-state-machines) page for the full guide.

## Comments

Line comments start with `#`:

```cure
# This is a comment
fn add(a: Int, b: Int) -> Int = a + b  # inline comment
```

## Complete example

```cure
mod MyApp.Math
  use Std.{Result, Option}

  type Sign = Positive | Negative | Zero

  fn factorial(n: Int) -> Int
    | 0 -> 1
    | n -> n * factorial(n - 1)

  fn classify(x: Int) -> Sign
    | x when x > 0 -> Positive
    | x when x < 0 -> Negative
    | _             -> Zero

  fn safe_divide(a: Int, b: {x: Int | x != 0}) -> Int = a / b

  fn sum(xs: List(Int)) -> Int =
    Std.List.foldl(xs, 0, fn(x) -> fn(acc) -> acc + x)

  fn main() -> Int = factorial(10)
```
