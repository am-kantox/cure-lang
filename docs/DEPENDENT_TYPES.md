# Cure Dependent Types Guide
This guide covers the dependent-typing layer added in v0.17.0:
Sigma types (dependent pairs), Pi types (dependent function types),
propositional equality, implicit arguments and unification, type-level
reduction, hole-driven development, and totality checking.
## 1. The big picture
Cure is *gradually dependently typed*. You may use the entire language
without ever encountering a dependent type, and you can opt in to as
much rigour as you need on a per-function basis. The mechanisms below
exist to make it possible to:
- Express invariants that survive into type-checked code.
- Carry small proofs alongside data.
- Get the type checker to *help* you write code interactively.
- Decide when a function is total enough to live in type-level computation.
## 2. Sigma types -- dependent pairs
A Sigma type pairs a value with a type that may depend on it.
```cure
type Sized(T) = Sigma(n: Nat, Vector(T, n))
```
The first component is a natural number `n`; the second component is
a vector of `T` of length exactly `n`. The bound name `n` is in scope
in the second component.
Cure recognises three surface forms:
- `Sigma(T1, T2)` -- non-dependent.
- `Sigma(name: T1, T2)` -- dependent; `name` is bound in `T2`.
- `DPair(...)` -- alias for `Sigma(...)` with the same conventions.
Internally, `Cure.Types.Sigma` represents these as
`{:sigma, var, fst_type, snd_ast}`.
### Subtyping
- Sigma types subtype componentwise.
- A Sigma forgets its dependency to become a plain tuple type.
- A plain tuple promotes to a Sigma when the components match.
## 3. Pi types -- dependent function types
A Pi type is a function whose return type may depend on its arguments:
```cure
fn append(xs: Vector(T, m), ys: Vector(T, n)) -> Vector(T, m + n)
```
The result type literally references the parameter names `m` and `n`.
At every call site, the type checker:
1. Substitutes the call-site argument expressions into the return-type
   AST.
2. Normalises the resulting expression with `Cure.Types.Reduce`.
3. Resolves the normalised AST back to a concrete `Cure.Types.Type`.
This means `append(va, vb)` where `va : Vector(T, 3)` and
`vb : Vector(T, 5)` is checked against `Vector(T, 8)` *without ever
calling SMT*.
Internal representation: `{:pi, [{name, type, mode}], ret_ast}` where
`mode` is one of `:explicit`, `:implicit`, `:erased`.
### Backward compatibility
Plain `{:fun, params, ret}` is treated as Pi with anonymous explicit
parameters and a return type that ignores its arguments. Existing
code paths in the type checker keep working unchanged.
## 4. Propositional equality
`Eq(T, a, b)` is the type of proofs that `a` and `b` are equal at
type `T`. There is exactly one constructor:
```cure
refl(x) : Eq(T, x, x)
```
and exactly one eliminator:
```cure
rewrite eq in expr
```
which substitutes equal terms in the goal type while type-checking
`expr`.
### Runtime erasure
Equality types and their proofs vanish at runtime. `refl(x)` lowers
to the atom `:cure_refl`; `rewrite eq in expr` lowers to `expr`
unchanged. The entire mechanism lives in the type checker.
### `Std.Equal`
The standard library exposes the basic combinators:
- `refl(x)` -- reflexivity.
- `sym(eq)` -- symmetry.
- `trans(p, q)` -- transitivity.
- `cong(f, eq)` -- congruence under a function.
## 5. Implicit arguments and unification
Implicit arguments use `{T}` braces in signatures:
```cure
fn id({T}, x: T) -> T = x
fn append({T}, {m: Nat}, {n: Nat},
          xs: Vector(T, m), ys: Vector(T, n)) -> Vector(T, m + n)
```
At each call site, `Cure.Types.Unify` solves the implicit values from
the explicit-argument types using first-order unification with an
occurs check. Unsolvable implicits become explicit type errors carrying
a structured **unification trace** that the LSP renders in hover and
the CLI prints in errors.
Implicit arguments are *erased* at codegen: they cost nothing at
runtime.
## 6. Type-level reduction
`Cure.Types.Reduce` is a small, terminating normaliser for type-level
expressions. It folds:
- Integer arithmetic (`+`, `-`, `*`, `/`, `%`).
- Float arithmetic (same operators on floats).
- Booleans (`and`, `or`, `not`).
- Comparisons over literals.
- `fst`/`snd` projection over literal tuples.
- Free-variable substitution.
This gives definitional equality for closed type-level expressions:
`Vector(T, 2 + 3)` is the same type as `Vector(T, 5)` without an
SMT call. SMT is still the fallback when reduction is not enough.
## 7. Hole-driven development
A *hole* is a placeholder for an as-yet-unwritten expression that the
type checker should *report on*, not silently accept.
- `?name` -- named hole.
- `??` -- anonymous hole, numbered `?_1`, `?_2`, ... in source order.
At each hole the checker emits a `:hole_goal` pipeline event carrying:
- the **goal type** at the hole position;
- the **local context** -- every variable in scope and its type.
The LSP turns hole reports into hover popups and inlay hints; the REPL
exposes them through the `:holes` command.
## 8. Totality / termination
`Cure.Types.Totality` classifies every function as `:total`, `:partial`,
or `:unknown`:
- **Coverage** -- every clause-set must cover all input shapes (we
  reuse `Cure.Types.PatternChecker`).
- **Termination** -- direct recursive calls must reduce a structural
  argument (`n - 1` of a pattern variable `n`, the tail of a list
  pattern, etc.).
The default behaviour is to *report* the classification, not reject
the program. Add `#[total]` above a function to upgrade the report to
a compile-time error if the function is not total.
v0.17.0 only handles direct recursion. Mutual recursion is deferred to
v0.18.0.
## 9. Refinement upgrades
Refinement types now compose with the rest of the dependent layer:
- **Path-sensitive refinement** -- inside `if` and `match` arms, the
  type of any variable referenced in the guard is refined for the
  duration of that path. See `Cure.Types.PathRefinement`.
- **`Std.Refine`** -- a stdlib module of common refinement aliases:
  `NonZero`, `Positive`, `Negative`, `NonNegative`, `Percentage`,
  `Probability`, ...
- The refinement subtype check still uses Z3 in the background.
## 10. Tying it all together
The full dependent-typing toolbox:
| Goal | Tool |
|---|---|
| Pair a value with a dependent type | `Sigma` |
| Function whose return type depends on args | `Pi` + `Reduce` |
| Carry a proof that two terms are equal | `Eq`, `refl`, `rewrite` |
| Hide boilerplate type/value parameters | `{T}` implicit + `Unify` |
| Get type-level integer arithmetic for free | `Reduce` |
| Sketch a function and ask the checker for help | `?name`, `??`, `:hole_goal` |
| Confirm a function never gets stuck | `Totality` + `#[total]` |
| Constrain values at the type level | refinement types + `Std.Refine` |
The fingertip rule: **reach for refinements first, Sigma when shape
matters, Pi when the return type computes from the args, Eq when you
need to share a fact between two pieces of code, holes when you don't
yet know what to write.**
