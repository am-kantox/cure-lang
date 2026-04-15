# Cure Type System

## Overview

Cure has a bidirectional type system with support for:

- Primitive types and composite types
- Algebraic data types (ADTs / sum types)
- Refinement types with SMT-backed verification
- Protocol-based ad-hoc polymorphism
- Pattern exhaustiveness checking

## Bidirectional Type Checking

The type checker operates in two modes:

- **Infer mode**: determines the type of an expression from its structure
- **Check mode**: verifies an expression has an expected type

Functions are checked in two passes:
1. Collect all function signatures (name, parameter types, return type)
2. Check each function body against its declared return type

## Primitive Types

- `Int` -- arbitrary-precision integers
- `Float` -- IEEE 754 floating point
- `String` -- UTF-8 binary strings
- `Bool` -- `true` or `false`
- `Atom` -- Erlang atoms (`:ok`, `:error`)
- `Char` -- single Unicode character
- `Unit` -- no meaningful value (`nil`)

## Subtyping

- `Int <: Float` (numeric widening)
- `Never <: T` for all T (bottom type)
- `T <: Any` for all T (top type)
- `{x: Int | P(x)} <: Int` (refinement drops constraint)
- `List(A) <: List(B)` if `A <: B` (covariant)
- `(A -> B) <: (C -> D)` if `C <: A` and `B <: D` (contravariant params)

## Refinement Types

Refinement types constrain a base type with a logical predicate:

```cure
type NonZero = {x: Int | x != 0}
type Positive = {x: Int | x > 0}
type Percentage = {p: Int | p >= 0 and p <= 100}
```

### Subtype Verification

Refinement subtyping is verified at compile time using Z3:

- `Positive <: NonZero` because `forall x. x > 0 => x != 0` (proven by Z3)
- `Percentage <: NonNegative` because `forall p. (p >= 0 and p <= 100) => p >= 0`
- `NonZero` is NOT `<: Positive` (counterexample: x = -1)

### Satisfiability

The compiler verifies refinement types are not empty:

- `{x: Int | x > 0}` is satisfiable (x = 1 works)
- `{x: Int | x > 0 and x < 0}` is unsatisfiable (warning)

## Pattern Exhaustiveness

The type checker analyzes match expressions for completeness:

- `Bool`: requires `true` and `false`
- `Result(T, E)`: requires `Ok(...)` and `Error(...)`
- `Option(T)`: requires `Some(...)` and `None()`
- `List(T)`: requires `[]` and `[_ | _]`
- Infinite types (`Int`, `String`): require a wildcard `_`

Non-exhaustive matches produce compile-time warnings.

## Guard-Based Type Refinement

When a function has a guard, parameter types are refined within the body:

```cure
fn process(x: Int) -> Int when x > 0 =
  # Inside this body, x has type {x: Int | x > 0}
  x * 2
```

For multi-clause functions, the type checker uses SMT to verify
guard coverage and detect unreachable clauses.

## Protocols

Protocols provide ad-hoc polymorphism. The type checker:

1. Registers protocol method signatures during the first pass
2. Validates implementation method signatures match the protocol
3. Checks implementation bodies against declared types
