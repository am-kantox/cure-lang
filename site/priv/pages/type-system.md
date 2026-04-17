%{
  title: "Type System",
  description: "Bidirectional checking, refinement types, dependent types (Sigma, Pi, equality), implicit arguments, holes, totality.",
  order: 3
}
---
Cure has a bidirectional type system with refinement types verified at compile time by the Z3 SMT solver and a compact **dependent-type** core: Sigma and Pi types, propositional equality, implicit arguments, holes, and totality classification. Types are checked statically -- no runtime type tags, no casts.

See the dedicated [Dependent types](#dependent-types) section for the language-level proof features landed in {{cure_vversion}}.

## Bidirectional type checking

The type checker operates in two modes:

- **Infer mode**: determines the type of an expression from its structure. Literals, variables, operators, and function calls are inferred.
- **Check mode**: verifies that an expression has an expected type. Function bodies are checked against their declared return type. Arguments are checked against parameter types.

Modules are checked in two passes:

1. **Signature collection**: scan all function definitions, collecting their names, parameter types, and return types. This allows mutual recursion -- functions can reference each other regardless of definition order.
2. **Body checking**: check each function body against its declared return type using check mode.

```cure
mod Example
  # Pass 1 registers: add : (Int, Int) -> Int, double : Int -> Int
  # Pass 2 checks each body

  fn add(a: Int, b: Int) -> Int = a + b

  fn double(x: Int) -> Int = add(x, x)
```

## Primitive types

- `Int` -- arbitrary-precision integers (BEAM big integers)
- `Float` -- IEEE 754 double-precision floating point
- `String` -- UTF-8 binary strings
- `Bool` -- `true` or `false`
- `Atom` -- Erlang atoms (`:ok`, `:error`, `:my_atom`)
- `Pid` -- Erlang process identifier
- `Char` -- single Unicode character
- `Unit` -- the type of `nil`, meaning "no meaningful value"

```cure
fn example() -> Int = 42
fn pi() -> Float = 3.14
fn name() -> String = "Alice"
fn flag() -> Bool = true
fn status() -> Atom = :ok
fn nothing() -> Unit = nil
```

## Composite types

- `List(T)` -- linked list, parameterized by element type
- `Map(K, V)` -- hash map
- `%[A, B]` -- tuple (fixed-size, heterogeneous)
- `A -> B` -- function type (from A to B)

```cure
fn numbers() -> List(Int) = [1, 2, 3]
fn lookup() -> Map(String, Int) = %{name: 42}
fn pair() -> %[Int, String] = %[1, "hello"]
fn adder() -> Int -> Int = fn(x) -> x + 1
```

Function types with multiple parameters are curried:

```cure
# Type of a two-argument function
fn make_adder() -> Int -> Int -> Int = fn(a) -> fn(b) -> a + b
```

## Algebraic data types

Sum types are defined with `type` and used as first-class values:

```cure
type Option(T) = Some(T) | None
type Result(T, E) = Ok(T) | Error(E)
type Color = Red | Green | Blue
```

Constructors are typed as functions:

- `Some : T -> Option(T)`
- `None : Option(T)` (nullary)
- `Ok : T -> Result(T, E)`
- `Red : Color` (nullary)

## Subtyping

Cure defines these subtype relationships:

- `Int <: Float` -- numeric widening (integers can be used where floats are expected)
- `Never <: T` for all T -- the bottom type is a subtype of everything
- `T <: Any` for all T -- every type is a subtype of the top type
- `{x: Int | P(x)} <: Int` -- a refinement type is a subtype of its base type (dropping the constraint)
- `List(A) <: List(B)` if `A <: B` -- lists are covariant
- `(A -> B) <: (C -> D)` if `C <: A` and `B <: D` -- function types are contravariant in parameters and covariant in return types

Examples of what this means in practice:

```cure
type Positive = {x: Int | x > 0}

# Positive <: Int, so this is valid:
fn double(x: Int) -> Int = x * 2
fn use_positive(p: Positive) -> Int = double(p)

# Int is NOT <: Positive, so this would be a type error:
# fn bad(x: Int) -> Positive = x  -- error!
```

## Refinement types

Refinement types constrain a base type with a logical predicate. The predicate is a boolean expression over the bound variable:

```cure
type NonZero = {x: Int | x != 0}
type Positive = {x: Int | x > 0}
type Percentage = {p: Int | p >= 0 and p <= 100}
type NonNegative = {x: Int | x >= 0}
type SmallInt = {n: Int | n >= 0 and n <= 255}
```

Predicates can use comparison operators (`==`, `!=`, `<`, `>`, `<=`, `>=`), boolean connectives (`and`, `or`, `not`), and arithmetic (`+`, `-`, `*`).

### Subtype verification via SMT

Refinement subtyping is verified at compile time by sending logical implications to Z3. To check whether `{x: A | P(x)} <: {x: A | Q(x)}`, the compiler asks Z3 to prove: `forall x. P(x) => Q(x)`.

Verified relationships:

- **Positive <: NonZero** -- because `forall x. x > 0 => x != 0` (Z3 proves `unsat` for the negation)
- **Percentage <: NonNegative** -- because `forall p. (p >= 0 and p <= 100) => p >= 0`
- **SmallInt <: NonNegative** -- because `forall n. (n >= 0 and n <= 255) => n >= 0`

Rejected relationships:

- **NonZero is NOT <: Positive** -- Z3 finds the counterexample `x = -1` (satisfies `x != 0` but not `x > 0`)
- **NonNegative is NOT <: Percentage** -- counterexample: `x = 101`

```cure
type NonZero = {x: Int | x != 0}
type Positive = {x: Int | x > 0}

fn needs_nonzero(x: NonZero) -> Int = x * 2

# This is valid: Positive <: NonZero
fn use_positive(p: Positive) -> Int = needs_nonzero(p)

# This would be a type error: NonZero is NOT <: Positive
# fn needs_positive(x: Positive) -> Int = x
# fn bad(n: NonZero) -> Int = needs_positive(n)  -- error!
```

### Satisfiability checking

The compiler verifies that refinement types are not empty (i.e., at least one value satisfies the constraint). This catches impossible types at definition time:

- `{x: Int | x > 0}` -- satisfiable (e.g., `x = 1`)
- `{x: Int | x > 0 and x < 0}` -- unsatisfiable: the compiler emits a warning that this type is empty

## Dependent type verification at call sites

Functions with `when` guards register as constrained types. When called with literal or statically-known arguments, the compiler substitutes values into the guard predicate and sends it to Z3.

```cure
fn safe_divide(a: Int, b: Int) -> Int when b != 0 = a / b
fn positive_double(x: Int) -> Int when x > 0 = x * 2
```

At a call site:

```cure
fn main() -> Int =
  safe_divide(42, 7)    # OK: Z3 proves 7 != 0
  safe_divide(42, 0)    # Warning: guard constraint violated (b = 0, but b != 0 required)
  positive_double(5)    # OK: Z3 proves 5 > 0
  positive_double(-1)   # Warning: guard constraint violated
```

When the proof fails, the solver extracts a counterexample model from Z3's `(get-model)` output, showing the specific values that break the constraint:

```text
Warning: call to 'safe_divide': guard constraint may be violated
  Constraint: b != 0
  Counterexample: b = 0
```

When arguments are not statically known (e.g., from user input), the compiler reports that it cannot prove the constraint -- it is the programmer's responsibility to validate inputs.

## Dependent types

Starting with v0.17.0 Cure ships a compact dependent-type core. Types can depend on values, values can carry proofs, and the checker reduces closed type-level expressions without calling out to the SMT solver. The ingredients:

- **Sigma types** `Sigma(name: T1, T2)` -- dependent pairs whose second component's type may mention the first.
- **Pi types** `fn f(x: A, y: B(x)) -> C(x, y)` -- function types whose return type depends on the arguments.
- **Propositional equality** `Eq(T, a, b)` with constructor `refl` and eliminator `rewrite`.
- **Implicit arguments** solved by first-order unification with occurs check.
- **Holes** `?name` / `??` reporting goal type and local context.
- **Totality** classification (`:total | :partial | :unknown`) with the optional `#[total]` decorator.
- **Path-sensitive refinement** flowing through `if` and `match` guards.

### Sigma types (dependent pairs)

`Sigma(n: Nat, Vector(T, n))` is "a pair of a natural number and a vector of exactly that length." The second component's type mentions the first by name.

```cure
type NonEmpty(T) = Sigma(n: Nat, Vector(T, n + 1))

fn singleton(x: T) -> NonEmpty(T) = (0, [x])
```

`Cure.Types.Sigma` recognises the surface syntax, subtypes componentwise, and round-trips to plain tuples at runtime. Surface syntax `DPair` is accepted as a synonym.

### Pi types (dependent functions)

Return types may mention the arguments:

```cure
fn append(xs: Vector(T, m), ys: Vector(T, n)) -> Vector(T, m + n)
```

At each call site, the checker substitutes the actual arguments into the return type, normalises through `Cure.Types.Reduce` (a terminating folder for type-level arithmetic, booleans, comparisons, and pair projection), and resolves the result. `Vector(T, 2 + 3)` and `Vector(T, 5)` are the same type -- no SMT round-trip required.

Pi parameters have three modes: `:explicit` (the default), `:implicit` (resolved by unification, see below), and `:erased` (compile-time only, dropped at codegen).

### Propositional equality

`Eq(T, a, b)` is the type of proofs that two values of type `T` are equal. It has one constructor and one eliminator:

```cure
# refl builds a proof that x = x
fn reflexive(x: Int) -> Eq(Int, x, x) = refl(x)

# rewrite transports a value through an equality
fn transport(p: Eq(T, a, b), v: F(a)) -> F(b) = rewrite p in v
```

Equality proofs are runtime-erased via the `:cure_refl` atom. The stdlib module `Std.Equal` exposes `refl`, `sym`, `trans`, and `cong` for everyday proof combinators.

### Implicit arguments and unification

Implicit parameters use brace syntax:

```cure
fn id({T}, x: T) -> T = x
fn identity_int() -> Int = id(42)    # {T} solved to Int
```

At each call site, first-order unification with an occurs check (`Cure.Types.Unify`) solves the implicit arguments from the explicit ones. When unification fails, the compiler emits a `:unification_trace` pipeline event pointing at the offending argument, position, and prior substitution. The LSP renders the trace in hover; the CLI prints it in error output. Implicit parameters are erased at codegen: they cost nothing at runtime.

### Holes and hole-driven development

A hole is a placeholder that asks the type checker to report what type would fit there.

```cure
fn safe_head(xs: List(T)) -> T = ?body
```

Compiling reports:

```text
?body : T
in scope:
  xs : List(T)
```

Anonymous `??` holes are numbered `?_1`, `?_2`, ... in source order. Every hole encountered during checking emits a `:hole_goal` event carrying both the goal type and the local context. The REPL's `:holes` meta-command lists every hole recorded during the last evaluation.

### Totality

A function is **total** when it terminates on every input and its pattern matching is exhaustive. `Cure.Types.Totality` classifies every function as `:total`, `:partial`, or `:unknown`, combining coverage (via `Cure.Types.PatternChecker`) with a structural-recursion check. The default is report-only. Decorating with `#[total]` upgrades the classification to a hard requirement:

```cure
#[total]
fn factorial(n: Nat) -> Nat
  | 0 -> 1
  | n -> n * factorial(n - 1)
```

Direct structural recursion is verified in v0.17.0; mutual recursion is scheduled for v0.19.0.

### Path-sensitive refinement

Refinement information now flows along `if` and `match` guards. `Cure.Types.PathRefinement` accumulates the branch condition (and its negation on the `else` side) into the type environment.

```cure
if x != 0 then 100 / x else 0
```

Inside the `then` branch, `x` is refined to `{x: Int | x != 0}`, so the division is safe without an explicit refinement annotation. The stdlib module `Std.Refine` ships ready-made refinements for everyday use: `NonZero`, `Positive`, `Negative`, `NonNegative`, `Percentage`, `Probability`, and predicate helpers.

### Error codes

The dependent-type machinery contributes a dedicated range of error codes `E011`-`E020` (implicit-argument failures, sigma destructuring, totality failures, unfilled holes, refinement counterexamples, dependent-type mismatches, equality-proof mismatches, doctest mismatches).

v0.18.0 adds codes `E021`-`E025` for the pattern engine: unknown record field in a pattern, record-pattern field type mismatch, non-literal map-pattern key, unbound pin variable, and non-exhaustive nested match. Every code has a detailed explanation available via `cure explain Edd` or `cure why Edd`.

## Pattern exhaustiveness

The type checker analyzes `match` expressions for completeness. Missing cases produce compile-time warnings.

### Bool

Requires both `true` and `false`:

```cure
fn describe(b: Bool) -> String =
  match b
    true -> "yes"
    false -> "no"
# Exhaustive: Bool has exactly two values
```

### Result(T, E)

Requires `Ok(...)` and `Error(...)`:

```cure
fn handle(r: Result(Int, String)) -> Int =
  match r
    Ok(v) -> v
    Error(_) -> -1
# Exhaustive: covers both constructors
```

### Option(T)

Requires `Some(...)` and `None()`:

```cure
fn unwrap(opt: Option(Int)) -> Int =
  match opt
    Some(v) -> v
    None() -> 0
# Exhaustive
```

### List(T)

Requires `[]` (empty) and `[_ | _]` (non-empty):

```cure
fn head_or_zero(xs: List(Int)) -> Int =
  match xs
    [h | _] -> h
    [] -> 0
# Exhaustive: covers empty and non-empty
```

### Infinite types

Types with infinite inhabitants (`Int`, `String`, `Float`) require a wildcard `_` to be exhaustive:

```cure
fn describe(x: Int) -> String
  | 0 -> "zero"
  | 1 -> "one"
  | _ -> "other"
# The wildcard is required -- you cannot enumerate all integers
```

Without the wildcard, the compiler warns:

```text
Warning: non-exhaustive patterns in function 'describe'
  Missing: wildcard (_) for infinite type Int
```

### Nested patterns

Exhaustiveness analysis works through nested constructors:

```cure
fn nested(x: Option(Result(Int, String))) -> Int =
  match x
    Some(Ok(v)) -> v
    Some(Error(_)) -> -1
    None() -> 0
# Exhaustive: all three paths covered
```

v0.18.0 adds a **Maranget-style** column walker for tuple scrutinees whose
element types are enumerable (Bool, Result, Option). Missing witnesses are
rendered as source-shaped strings and reported under code `E025`:

```text
Warning: match expression has nested non-exhaustive cases (E025)
  missing: %[Error(_), _]
```

The original flat classifier is kept as a fast-path for simple,
single-level matches.

## Guard-based flow typing

When a function has a `when` guard, parameter types are refined within the guarded body. The type checker narrows the type to include the guard constraint:

```cure
fn process(x: Int) -> Int when x > 0 =
  # Inside this body, x has type {x: Int | x > 0}
  x * 2
```

For multi-clause functions with guards, the type checker uses SMT to verify guard coverage and detect unreachable clauses:

```cure
fn classify(x: Int) -> String
  | x when x > 0 -> "positive"
  | x when x < 0 -> "negative"
  | _ -> "zero"
# Guards cover all integers: x > 0, x < 0, and the wildcard for x == 0
```

If a guard is unreachable (e.g., implied by a previous clause), the compiler warns about dead code.

## Record types

Records introduce named product types. The type checker tracks them with a
lightweight `{:named, "TypeName"}` representation that preserves the record
name instead of collapsing it to `Any`.

### How records are type-checked

The checker runs in two passes. In the first pass, every `rec` definition
registers its field schema in the type environment:

```
rec Point        ->  "Point" : %{"x" => Int, "y" => Int}
rec Person       ->  "Person" : %{"name" => String, "age" => Int}
rec Rectangle    ->  "Rectangle" : %{"origin" => Point, "width" => Int, ...}
```

In the second pass, this schema is available to type-check every operation:

**Construction** -- `Point{x: 3, y: 4}` produces type `Point`. The checker
verifies each field value against its declared type.

**Field access** -- `p.x` where `p : Point` produces type `Int` (looked up
from the schema). Field access on an `Any`-typed value produces `Any`.

**Record update** -- `Point{p | x: new_x}` where `p : Point`:
- Verifies `new_x` has type `Int` (the declared type of `Point.x`)
- Returns `Point`
- Compiles to the BEAM map-update instruction, preserving all unlisted fields including `__struct__`

**Function parameters** -- `fn f(p: Point)` makes `p` available as type
`Point` inside the body, so `p.x` correctly infers `Int`.

### Subtyping

Named record types participate in subtyping:

```cure
# Point <: Any (universal rule)
fn accepts_any(x: Any) -> Any = x
fn use_point(p: Point) -> Any = accepts_any(p)  # valid

# Point is the same type as Point (reflexivity)
fn same_point(p: Point) -> Point = p  # valid
```

Named types are NOT subtypes of each other unless they are the same type.
There is no structural record subtyping -- a record with fields `{x: Int, y: Int}`
is not implicitly a subtype of one with fields `{x: Int}` in the current type
system.

### Examples

```cure
mod Geometry
  rec Point
    x: Int
    y: Int

  # Construction: typed as Point
  fn origin() -> Point = Point{x: 0, y: 0}

  # Field access: p.x -> Int, p.y -> Int
  fn distance_squared(a: Point, b: Point) -> Int =
    let dx = b.x - a.x
    let dy = b.y - a.y
    dx * dx + dy * dy

  # Record update: returns Point
  fn translate(p: Point, dx: Int, dy: Int) -> Point =
    Point{p | x: p.x + dx, y: p.y + dy}

  # Wrong field type -> type error at compile time
  # fn bad(p: Point) -> Point = Point{p | x: "not an int"}  -- error!
```

## Protocols and type checking

Protocols provide ad-hoc polymorphism. The type checker:

1. Registers protocol method signatures during the first pass (signature collection)
2. Validates that each `impl` method signature matches the protocol declaration
3. Checks implementation bodies against the declared types

```cure
proto Eq(T)
  fn eq(a: T, b: T) -> Bool

impl Eq for Int
  fn eq(a: Int, b: Int) -> Bool = a == b

# The type checker verifies:
# - eq in impl Eq for Int matches the signature fn eq(a: T, b: T) -> Bool
#   with T = Int
# - The body (a == b) has type Bool, matching the declared return type
```

Protocol implementations are registered globally in an ETS table during compilation, enabling cross-module dispatch.

## Effect system

Cure tracks side effects in the type system. Functions can declare their effects after the return type using `!`:

```cure
fn read_file(path: String) -> String ! Io
fn risky(x: Int) -> Int ! Exception
fn complex(x: Int) -> Int ! Io, Exception
```

### Effect kinds

Five effect kinds form a closed set:

- `Io` -- I/O operations (printing, file access)
- `State` -- mutable state (send, receive, process dictionary)
- `Exception` -- exception throwing
- `Spawn` -- process spawning
- `Extern` -- unclassified foreign function calls

### Inference

Effect annotations are optional. When omitted, the type checker infers effects from the function body by analyzing:

- Keywords: `send`/`receive` -> State, `throw` -> Exception, `spawn` -> Spawn
- `@extern` targets: classified by Erlang module (`:io` -> Io, `:gen_server` -> State, etc.)
- Transitive calls: calling an effectful function inherits its effects

### Effect subtyping

A pure function (no effects) is a subtype of any effectful function with the same signature:

```
(Int) -> Int  <:  (Int) -> Int ! Io
```

An effectful function is a subtype of another effectful function only when its effect set is a subset:

```
(Int) -> Int ! Io  <:  (Int) -> Int ! Io, State
```

This means pure callbacks can be passed where effectful ones are expected.
