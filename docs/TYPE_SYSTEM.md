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

## Record types

Records introduce named product types. The type checker represents them as
`{:named, "TypeName"}` -- a lightweight reference that carries the original
name without erasing it to `Any`.

### Schema registration

The checker's first pass (`collect_signatures`) registers each `rec` definition
in `Env.types`:

```
"Point" -> {:record, :point, %{"x" => :int, "y" => :int}}
"Person" -> {:record, :person, %{"name" => :string, "age" => :int}}
```

This schema is available during the second pass so that field accesses and
record updates can be type-checked against the declared field types.

### Typing rules

- **Construction** -- `Point{x: 3, y: 4}` has type `{:named, "Point"}`.
- **Field access** -- `p.x` where `p : {:named, "Point"}` has type `:int`
  (looked up from the registered schema). Field access on `Any` produces `Any`.
- **Record update** -- `Point{p | x: new_x}` where `p : {:named, "Point"}`
  type-checks each override value against the declared field type and returns
  `{:named, "Point"}`.
- **Parameters** -- `fn f(p: Point)` resolves `Point` to `{:named, "Point"}`,
  making `p` available with full field-type information in the body.

### Subtyping for named types

`{:named, Name}` participates in the subtype hierarchy:

- `{:named, T} <: Any` for all T (inherited from the universal rule)
- `{:named, "Pair"} <: {:adt, :pair, _params}` when
  `String.downcase("Pair") == "pair"` -- named types satisfy their
  corresponding parameterized ADT return type (e.g. `fn f() -> Pair(A, B)`
  is satisfied by a body of type `{:named, "Pair"}`)
- `{:named, T} <: {:named, T}` (reflexivity, from `subtype?(t, t)`)

## Protocols

Protocols provide ad-hoc polymorphism. The type checker:

1. Registers protocol method signatures during the first pass
2. Validates implementation method signatures match the protocol
3. Checks implementation bodies against declared types

## Sigma, Pi, equality, holes, totality (v0.17.0)

See `DEPENDENT_TYPES.md` for the full guide. Brief summary:

- **Sigma types** -- `{:sigma, var, fst_type, snd_ast}` -- dependent
  pairs where the second component's type may reference the first
  component's value. Surface syntax: `Sigma(name: T1, T2)`.
- **Pi types** -- `{:pi, [{name, type, mode}], ret_ast}` -- dependent
  function types. Return types may reference parameter names; the
  checker substitutes and normalises at every call site.
- **Equality types** -- `{:eq, T, a, b}` -- proofs that `a == b` at
  type `T`. Constructor `refl(x)`, eliminator `rewrite eq in expr`.
  Erased at runtime.
- **Holes** -- `?name` and `??` placeholders. The checker emits a
  `:hole_goal` event with the goal type and local context.
- **Totality** -- `Cure.Types.Totality.classify/1` returns `:total`,
  `:partial`, or `:unknown`. The `#[total]` decorator upgrades the
  classification to a hard requirement.
- **Type-level reduction** -- `Cure.Types.Reduce.normalize/2` folds
  arithmetic, boolean, and projection operations on closed type-level
  expressions; this gives definitional equality before the checker
  falls back to SMT.
- **Unification** -- `Cure.Types.Unify` solves implicit arguments via
  first-order unification with an occurs check; failures emit a
  `:unification_trace` event.
- **Path-sensitive refinement** -- `Cure.Types.PathRefinement` extracts
  refinements from `if`/`match` guards and applies them to in-scope
  variables along the matching branch.
