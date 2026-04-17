# Cure v0.17.0 -- Proofs & Polish: Toward Idris

Cure is a dependently-typed programming language for the BEAM virtual
machine with first-class finite state machines and SMT-backed
verification.

v0.17.0 raises the dependent-typing layer from "refinements + token-level
dependent params" to "first-class small dependently-typed core" while
also making the language considerably more pleasant to live in
day-to-day. Three themes were delivered together.

## Theme A -- Dependent-type maturation

- **Sigma types** (`Cure.Types.Sigma`) -- dependent pairs surfaced via
  `Sigma(name: T1, T2)` and `DPair(...)`. Recognised by `Type.resolve/1`,
  participates in subtyping.
- **Pi types** (`Cure.Types.Pi`) -- a richer function-type form that
  carries parameter names and modes (`:explicit`, `:implicit`, `:erased`)
  and a return-type AST that may reference the parameters.
- **Type-level reduction** (`Cure.Types.Reduce`) -- a small terminating
  normaliser for arithmetic, boolean, comparison, and pair projection
  on closed type-level expressions. Used to compare dependent return
  types without invoking SMT for trivial cases.
- **Propositional equality** (`Cure.Types.Equality`, `Std.Equal`) --
  `Eq(T, a, b)` carries proofs of `a == b`. `refl(x)` is the only
  constructor; `rewrite eq in expr` is the only eliminator. Erased at
  runtime.
- **Implicit arguments + unification** (`Cure.Types.Unify`) --
  first-order unification with occurs check. Implicit-argument
  inference solves `{T}` bindings from explicit-argument types at
  every call site. Failures emit a structured `:unification_trace`
  pipeline event.
- **Hole-driven development** (`Cure.Types.Holes`) -- `?name` and `??`
  placeholders that the type checker reports on rather than silently
  accepts. Each hole emits a `:hole_goal` event carrying the goal
  type and the local context.
- **Totality / termination** (`Cure.Types.Totality`) -- coverage +
  structural-recursion analysis. Classifies functions as `:total`,
  `:partial`, or `:unknown`. The `#[total]` decorator upgrades the
  classification to a hard requirement.
- **Refinement upgrades** (`Cure.Types.PathRefinement`, `Std.Refine`)
  -- path-sensitive refinement extracted from `if`/`match` guards;
  a stdlib of common refinement aliases (`NonZero`, `Positive`,
  `Percentage`, `Probability`, ...).

## Theme B -- Hole-driven, friction-free UX

- **REPL upgrade** (`Cure.REPL`) -- multi-line input, meta-commands
  (`:t`, `:doc`, `:effects`, `:load`, `:reload`, `:use`, `:holes`,
  `:env`, `:reset`, `:fmt`, `:help`, `:quit`), history persisted to
  `~/.cure_history`.
- **Watch mode** (`Cure.Watch`, `cure watch`) -- recompile, type-check,
  or test on every file change. 200 ms debounce.
- **LSP polish** (`Cure.LSP.Server`) -- inlay hints, signature help,
  formatting, prepareRename / rename, code lenses, semantic tokens,
  workspace symbols.
- **Error catalog expansion** (`Cure.Compiler.Errors`) -- new codes
  `E011`-`E020` covering implicit argument failures, sigma destructuring,
  totality failures, hole reports, refinement counterexamples,
  dependent-type mismatches, equality proof mismatches, doctest
  mismatches, and more. `cure explain Eddd` and `cure why Eddd`
  surface the catalog.
- **Project & tooling** -- `cure new <name> [--lib | --app | --fsm]`
  with three templates; `Cure.lock` lockfile; `cure deps update`,
  `cure deps tree`; git-based dependencies via
  `Cure.Project.resolve_git_dep/2`; `cure bench`; `cure test --filter`
  / `--doctests`.
- **Doctests** (`Cure.Doc.Doctests`) -- `##` blocks containing
  `cure>` / `=>` pairs are harvested and run by `cure test --doctests`.
- **Tutorial** (`docs/TUTORIAL.md`) -- ten progressive chapters plus
  a refreshed `LANGUAGE_SPEC.md`, `TYPE_SYSTEM.md`, `STDLIB.md`, and
  the new `DEPENDENT_TYPES.md`.

## Theme C -- Ecosystem groundwork

- **Hex publication metadata** -- `mix.exs` carries a complete
  `package` block, MIT license, CHANGELOG link; `LICENSE` file ships
  in the repo.
- **VS Code extension scaffold** (`vscode-cure/`) -- TypeScript
  language-client wrapper, TextMate grammar, language configuration,
  README. Marketplace publication deferred.
- **Package registry design** (`docs/PACKAGE_REGISTRY.md`) -- the
  contract for v0.18.0+ work: manifest, lockfile, resolver, index
  service, signing model.

## Numbers

- ~9 new modules and ~9 new test files; ~150 new tests on top of
  v0.16.0's 714 (all previous tests still pass).
- 2 new stdlib modules: `Std.Equal`, `Std.Refine` (total now 20).
- 6 new examples: `sigma_pairs.cure`, `length_indexed.cure`,
  `equality_proofs.cure`, `holes_demo.cure`, `totality.cure`,
  `doctest_demo.cure`.
- 3 new docs: `docs/DEPENDENT_TYPES.md`, `docs/TUTORIAL.md`,
  `docs/PACKAGE_REGISTRY.md`.

## Naming

The release is titled **"Proofs & Polish"**, subtitled *Toward Idris*.

---

# v0.18.0 plan -- "Bring the Furniture"

The v0.17.0 release deliberately deferred a set of "new ideas" so the
dependent-typing core could land cleanly. v0.18.0 will bring them home.

## New language features

- **`proof` containers** -- a cousin of `mod`/`fsm`. Inside, every
  binding must elaborate to an `Eq` or refinement proof. The natural
  home for `Std.Proof.plus_zero`, `Std.Proof.append_assoc`, ...
- **`assert_type` builtin** -- `assert_type expr : T` becomes a
  compile-time type assertion that disappears at runtime. Useful
  for documentation and for catching regressions in type inference.
- **Records with default field values** --
  `rec Person\n  name: String = ""\n  age: Int = 0`. Lowers to map
  merges in codegen.
- **`@derive(Show, Eq, Ord)` shorthand on `rec`** -- finish wiring
  `Cure.Types.Derive` so the trio works end-to-end.

## New stdlib

- **Property-based testing in `Std.Test`** --
  `Std.Test.forall(generator, fn x -> property end)` with a tiny
  stateless QuickCheck-shaped generator API
  (`int_in/2`, `list_of/1`, `one_of/1`, ...).
- **`Std.Iter`** -- a lazy iterator protocol that lets `for`
  comprehensions be desugared lazily where types permit.

## Ecosystem

- The *first half* of the package registry sketched in
  `docs/PACKAGE_REGISTRY.md`: the `~>`/`>=`/`==` version-constraint
  parser, the resolver, and deeper `Cure.lock` semantics. The index
  service itself follows in v0.19.0.
- Mutual-recursion totality checking (single-file cycles), completing
  the totality work started in v0.17.0.
