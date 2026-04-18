# Cure v0.19.0 -- Bring the Furniture
*Ergonomics, proofs, and the first half of a registry.*

Cure is a dependently-typed programming language for the BEAM virtual
machine with first-class finite state machines and SMT-backed
verification.

v0.18.0 rebuilt pattern matching into a deeply-recursive engine.
v0.19.0 completes the "Bring the Furniture" slate that was deferred
to keep destructuring clean. The furniture, from largest piece to
smallest:

- `proof` containers for laws-as-programs.
- `assert_type expr : T` as a zero-runtime type-assertion wrapper.
- Records with default field values.
- `@derive(Show, Eq, Ord)` wired end-to-end on `rec`.
- Property-based testing: `Std.Gen` + `Std.Test.forall`.
- A lazy iterator protocol: `Std.Iter`.
- The first half of the package registry (version parser + resolver).
- Mutual-recursion totality (SCC + structural-decrease check).
- Multi-head cons patterns: `[a, b, c | rest]`.

## Language

### `proof` containers

```cure
proof Std.Proof
  fn plus_zero(_n: Int) -> Eq(Int, n, n) = :cure_refl
  fn append_nil(_xs: List(T)) -> Eq(List(T), xs, xs) = :cure_refl
```

A new `proof` keyword sits alongside `mod`/`fsm`. The container
compiles to a regular BEAM module, but every function's return type
must be `Eq(T, a, b)` or a refinement annotation. Runtime values are
the `:cure_refl` atom; the type checker does the work. Mismatches
surface as `E026`.

### `assert_type expr : T`

```cure
fn doubled(n: Int) -> Int = assert_type n * 2 : Int
```

A compile-time type assertion that disappears at runtime. If the
inferred type of `expr` does not fit `T`, the compiler emits `E027`.

### Record field defaults

```cure
rec Person
  name: String = "Anonymous"
  age: Int = 0
  active: Bool = true
```

Construction merges declared defaults with the user-supplied fields.
Overrides always win. Default type mismatches emit `E028`.

### `@derive(Show, Eq, Ord)`

```cure
@derive(Show, Eq, Ord)
rec Point
  x: Int
  y: Int
```

The decorator wires `Cure.Types.Derive` end to end: the synthesised
`show/1`, `eq/2`, and `compare/2` functions are plain module exports.

### Multi-head cons patterns

```cure
match xs
  [a, b, c | rest] -> a + b + c
  _                -> 0
```

The parser desugars multi-head cons to right-associated cells
(`[a | [b | [c | rest]]]`). Works in pattern and construction
positions.

## Standard library

- **`Std.Proof`** -- reflexivity-based arithmetic and list laws.
- **`Std.Gen`** -- `int_in/2`, `bool/0`, `one_of/2`, `list_of_int/3`,
  `list_int/3`. Backed by `:rand`.
- **`Std.Iter`** -- lazy iterator protocol. Constructors: `empty/0`,
  `from_list/1`, `range/2`. Consumers: `fold/3`, `take/2`,
  `to_list/1`.
- **`Std.Test.forall/3`** and **`Std.Test.forall_default/2`** --
  property-based runner. Raises `:property_failed` on first
  counterexample.

## Totality

`Cure.Types.Totality.check_mutual/1` runs a Tarjan SCC analysis over
a module's call graph. Non-trivial strongly-connected components are
reported as `:ok` (structural decrease proved) or `:suspect`
(`E029`).

## Packaging

- `Cure.Project.Version` -- SemVer parser with `~>`, `>=`, `<=`,
  `<`, `>`, `==`, compound constraints joined by `and`.
  MAJOR.MINOR is accepted as shorthand for MAJOR.MINOR.0.
- `Cure.Project.Resolver` -- deterministic backtracking resolver
  over a local/git workspace. Newest-compatible-first; conflicts
  surface as `E030`.

The remote registry index service is slated for v0.20.0.

## Error catalog

Five new codes: `E026` proof shape, `E027` assert_type failed,
`E028` record default mismatch, `E029` mutual recursion not
structural, `E030` package version conflict.

## Numbers

- 4 new Elixir modules: `Cure.Project.Version`, `Cure.Project.Resolver`,
  plus major extensions to `Cure.Types.Totality`, `Cure.Types.Derive`,
  `Cure.Compiler.Codegen`, `Cure.Compiler.Parser`, `Cure.Types.Checker`,
  `Cure.Types.Type`.
- 3 new stdlib modules (`Std.Proof`, `Std.Gen`, `Std.Iter`);
  `Std.Test` extended with `forall`.
- 4 new examples (`defaults.cure`, `derived_show.cure`,
  `proof_laws.cure`, `lazy_iter.cure`).
- 1 new documentation file (`docs/PROOFS.md`).
- New error codes `E026`--`E030`.
- Test count jumps from 923 to ~970, new tests spread across
  `pattern_compiler_test`, `record_defaults_test`, `assert_type_test`,
  `derive_integration_test`, `proof_test`, `totality_mutual_test`,
  `version_test`, `resolver_test`, `pbt_test`, `iter_test`,
  `multi_head_cons_test`.
- `mix credo --strict`: 0 issues.
- `mix cure.check.stdlib`: 24/24 modules clean.
- `mix cure.check.examples`: 30/30 programs clean.

## What's next

- **v0.20.0**: the second half of the package registry -- the remote
  index service, signing, and Hex.pm cross-publishing.
- Refinement narrowing through nested record/map patterns.
- Full bitstring-pattern segment specifiers in `PatternCompiler`.
- Type-directed `@derive` extensions (Functor, Monoid, JSON).

## Naming

"Bring the Furniture" -- subtitled *Ergonomics, proofs, and the first
half of a registry*.
