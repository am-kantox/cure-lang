# Cure Language Specification

## Syntax Overview

Cure is an indentation-structured language. Blocks are delimited by
indentation level, not by keywords like `do`/`end` or braces.

### Keywords

`fn`, `mod`, `rec`, `fsm`, `proto`, `impl`, `type`, `let`, `if`, `then`,
`else`, `elif`, `match`, `when`, `where`, `local`, `use`, `return`, `throw`,
`try`, `catch`, `finally`, `for`, `in`, `true`, `false`, `nil`,
`and`, `or`, `not`

### Identifiers

Identifiers may carry a trailing `?` to signal a predicate (Elixir
convention):

```cure
fn even?(n: Int) -> Bool = n % 2 == 0
fn is_empty?(xs: List(T)) -> Bool = ...
```

The `!` suffix is reserved for effect annotations and FSM hard
events.

### Comments and docstrings

- `# ...` -- line comment.
- `## text` -- single-line doc comment. One per line; attached to the
  following definition.
- `###\n...\n###` -- fenced multi-line doc comment. Opens on a line
  whose first three non-whitespace characters are `###`; closes on the
  next line whose first three non-whitespace characters are `###`.
  Leading indentation common to every body line is stripped.

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

**Multi-line layout (v0.21.0).** ADT declarations may span multiple
lines with leading `|` on continuation lines. The single-line and
multi-line forms are syntactically equivalent.

```cure
type Shape =
  | Circle(Int)
  | Square(Int)
  | Triangle(Int, Int, Int)
```

**Function-type payloads (v0.21.0).** Constructor payloads accept
arbitrary type expressions, including function arrows:

```cure
type Callback = On(Int -> Int) | Off
type Transform = Morph((Int, Int) -> Int) | Id
```

Function-typed payloads compile to first-class functions at runtime;
pattern matching binds the function to a variable you can call like
any other lambda.

### Refinement types

```cure
type NonZero = {x: Int | x != 0}
type Positive = {x: Int | x > 0}
type Percentage = {p: Int | p >= 0 and p <= 100}
```

Refinement type subtyping is verified at compile time using Z3.
With **path-sensitive refinement** (v0.17.0), the type of a variable
appearing in an `if`/`match` guard is refined for the duration of that
branch.

### Sigma types (dependent pairs)

```cure
type Sized(T) = Sigma(n: Nat, Vector(T, n))
```

A Sigma type pairs a value with a type that may depend on it.
The surface forms `Sigma(T1, T2)`, `Sigma(name: T1, T2)`, and
`DPair(...)` are all recognised.

### Pi types (dependent function types)

```cure
fn append(xs: Vector(T, m), ys: Vector(T, n)) -> Vector(T, m + n)
```

Return types may freely reference parameter names. The type checker
substitutes the call-site arguments and normalises the resulting
expression with `Cure.Types.Reduce` before comparing.

### Equality types

```cure
refl(x) : Eq(T, x, x)
```

`Eq(T, a, b)` is the type of proofs that `a == b` at type `T`.
`refl(x)` is the only constructor; `rewrite eq in expr` is the only
eliminator. All Eq values are erased at runtime.

### Implicit arguments

```cure
fn id({T}, x: T) -> T = x
```

Parameters in `{...}` braces are inferred from explicit-argument types
at each call site via `Cure.Types.Unify`. They cost nothing at runtime.

### Holes

```cure
fn safe_head(xs: List(T)) -> T = ?body
```

A `?name` or `??` placeholder triggers a `:hole_goal` pipeline event
that reports the goal type and the local context at the hole position.

### Totality

```cure
#[total]
fn factorial(n: Int) -> Int
  | 0 -> 1
  | n -> n * factorial(n - 1)
```

`Cure.Types.Totality` classifies every function as `:total`,
`:partial`, or `:unknown`. Add `#[total]` to upgrade the
classification to a compile-time error.

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
`match` (and `let`) support deep destructuring across every structural
form in the language. As of v0.18.0 the supported pattern shapes are:
### Literals and variables
```cure
match x
  0      -> "zero"
  n      -> "nonzero"
  _      -> "never reached"
```
`_` is the wildcard. A name starting with `_` (for example `_unused`)
is a binding that silences the unused-variable warning.
### Tuples and lists
```cure
match pair
  %[a, b]        -> a + b
  %[a, b, _rest] -> a + b

match xs
  []             -> "empty"
  [h | t]        -> "non-empty"
  [a, b, c]      -> "exactly three"
```
Cons is single-head only: `[h | t]` binds `h` to the head and `t` to
the tail. Matching against a literal-length list (`[a, b, c]`) requires
the list to have that exact length.
### Maps
```cure
match request
  %{method: "GET", path: p}    -> fetch(p)
  %{method: m, path: _}        -> reject(m)
```
Map keys in pattern position must be literal values. A map pattern
matches if every listed key is present in the subject; keys not
mentioned are ignored (open matching, like Elixir's `%{...}`).
### Records and field punning
```cure
match person
  Person{name, age}                    -> salute(name, age)
  Person{name, address: Address{city}} -> greet(name, city)
```
A bare identifier inside a record pattern is shorthand for
`name: name` (field punning). Record patterns compile to map patterns
with a `__struct__ := :tag` guard, so they only match values built
with the same record type.
### ADT constructors
```cure
match result
  Ok(v)         -> v
  Error(reason) -> default

match option
  Some(x) -> x
  None()  -> 0
```
Nullary constructors must be written with empty parentheses
(`None()`), never bare `None` -- a bare `None` is a fresh variable
binding.
### The pin operator `^x`
```cure
let target = get_tag()

match event.tag
  ^target -> :hit
  _       -> :miss
```
`^x` compares against a previously-bound value rather than binding
fresh. Lowered by the compiler to a guard `V_fresh =:= V_x`.
### Repeated variables
```cure
match pair
  %[x, x] -> :equal
  _       -> :different
```
A name that appears twice in the same pattern binds on its first
occurrence and is turned into an equality guard at every later
position (so the pattern only matches when all occurrences hold the
same value).
### Nested destructuring
Any combination of the above can be nested:
```cure
match value
  %[_, %{list: [head | tail]}, _] -> handle(head, tail)
  Person{name: n, address: Address{city: c, zip: _}} when c == "Madrid" ->
    greet(n)
```
### Exhaustiveness
The compiler checks pattern exhaustiveness. Shallow coverage gaps are
reported by the flat classifier (`E004`); nested gaps (tuples of ADTs,
records in tuples, etc.) are reported with a concrete witness under
code `E025`.

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

**In-place destructuring (v0.21.0).** `let` bindings support the same
pattern grammar as `match` arms: ADT constructors, tuples, cons
cells, record field punning, maps, and binary segments. Each bound
variable carries the narrowed scrutinee type.

```cure
let Ok(x)         = parse(input)       # ADT constructor
let %[a, b]       = pair                # tuple destructure
let [h | _rest]   = xs                  # cons destructure
let Point{x, y}   = p                   # record punning
let <<b, _::binary>> = buf              # binary destructure
```

Non-exhaustive `let` patterns emit code `E034` as a warning (not an
error): the binding still compiles, and Erlang's `=` raises at
runtime on a failed match. Setting `partial: true` on the assignment
metadata suppresses the warning.

### Binary patterns

Binary literals use Erlang-style segment grammar between `<<` and
`>>`. Every segment is `value [:: specifier_chain]`; the specifier
chain is hyphen-joined and covers type (`integer`, `float`, `utf8`,
`utf16`, `utf32`, `binary`, `bytes`, `bitstring`, `bits`),
signedness, endianness, `size(expr)`, and `unit(n)`. See
`docs/BINARIES.md` for the authoritative reference.

```cure
let header       = <<42, 1, 2, 3>>
let <<tag, _::binary>> = buffer

match frame
  <<len::16, payload::binary-size(len), _::binary>> -> payload
  <<>>                                              -> <<>>
```

Binary exhaustiveness is tracked via code `E031`.

### Pipe operator

```cure
5 |> double |> add(1)
# desugars to: add(double(5), 1)
```
