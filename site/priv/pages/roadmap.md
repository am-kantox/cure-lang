%{
  title: "Roadmap",
  description: "What's implemented, what's next, and what's planned for the future.",
  order: 8
}
---

## Implemented: v0.12.0

The first complete release. Full compilation pipeline from source to `.beam`.

- **Compilation pipeline** -- lexer, parser, type checker, code generator.
  Each stage emits structured events via PubSub.
- **Bidirectional type system** -- local type inference with annotation
  checking. Refinement types with constraints (`{x: Int | x > 0}`).
- **SMT integration** -- Z3 solver verifies refinement type constraints at
  compile time.
- **First-class FSMs** -- `fsm` blocks compile to OTP `gen_statem` modules
  with automatic reachability, deadlock freedom, and terminal state
  verification.
- **Protocol system** -- `proto`/`impl` with guard-based dispatch. Clauses
  ordered by type specificity (Bool before Atom).
- **Self-hosted stdlib** -- 12 modules written in Cure: Core, List, Math,
  String, Pair, Io, Show, Eq, Ord, System, Fsm, Result.
- **LSP server** -- diagnostics, hover, keyword completions over stdio.
- **MCP server** -- 7 tools for AI integration via JSON-RPC 2.0.
- **CLI** -- `cure compile`, `cure run`, `cure check`, `cure lsp`,
  `cure stdlib`, `cure version`.
- **Optimizer** -- 3 passes: constant fold, dead code elimination, pipe
  inline.
- **569 tests.** Zero Credo issues in strict mode. Zero compilation warnings.

## Implemented: v0.13.0

Dependent types get teeth. The compiler now proves constraints at call sites.

- **Dependent type verification at call sites** -- functions with `when`
  guards register as constrained types. At call sites, the compiler
  substitutes literals into the guard and sends the predicate to Z3. If
  unsatisfiable, you get a warning with a counterexample.
- **Cross-module protocol registry** -- global ETS table backing
  `register_impl`, `lookup_impl`, `has_impl?`. Every `impl` block registers
  during compilation, enabling cross-module dispatch resolution.
- **LSP: go-to-definition** -- jump to function and module definitions.
- **LSP: document symbols** -- hierarchical outline of modules, functions,
  protocols, FSMs.
- **LSP: code actions** -- quick-fix for non-exhaustive matches (add wildcard
  pattern) and did-you-mean suggestions for unbound variables.
- **5 optimizer passes** -- added inline (small pure non-recursive functions)
  and guard simplify (algebraic boolean rules).
- **FSM transition guards and actions** -- transitions support `when` guards
  and `do` actions: `State --event when cond do action--> NextState`.
- **Structured error catalog** -- error codes E001-E005 with `cure explain`.
  Errors show source location with caret display.
- **4 new stdlib modules** -- Map (14 fns), Set (11 fns), Option (10 fns),
  Functor (1 fn). Total: 17 modules, ~200 functions.
- **Std.Test** -- assertion primitives (`assert`, `assert_eq`, `assert_ne`,
  `assert_gt`, `assert_lt`). Total: 18 modules.
- **`cure test`** -- run test files from `test/`, compile and execute
  `test_*` functions.
- **`cure init`** -- scaffold a new project with `Cure.toml`.
- **`cure explain`** -- look up error code explanations.
- **606 tests.** Zero Credo issues. Zero compilation warnings. 48 Elixir
  source files.

## Implemented: v0.14.0

Package management, deeper type tracking, LSP type holes, incremental
parsing, cross-module protocol dispatch, and extended testing.

### Phase 1: Package management

Cure gets its own project file and dependency resolution.

- `Cure.toml` project file with `[project]`, `[dependencies]`, `[compiler]`
  sections. Parsed at `cure compile` / `cure run` time.
- `cure init <name>` scaffolds the project: `Cure.toml`, `lib/`, `test/`,
  and a hello-world `lib/main.cure`.
- `cure deps` resolves and compiles path-based dependencies, adding their
  `.beam` files to the code path.

### Phase 2: Deep dependent type tracking

Move beyond call-site literal substitution into full value tracking.

- **Type tracking through `let` bindings** -- bound variables carry their
  inferred types through the type environment for subsequent call-site
  checking.
- **Path-sensitive refinement** -- inside `if x > 0 then safe_div(10, x) else 0`,
  the checker applies the branch condition as a type assumption in the
  then-branch and its negation in the else-branch.
- **SMT context accumulation** -- guard conditions accumulate as type
  refinements in the environment as the checker descends into branches.

### Phase 3: LSP type holes

Interactive type inference via placeholder types.

- `_` in type annotation positions resolves to `{:type_hole, :infer}` and
  is compatible with any type (`subtype?(_, T)` and `subtype?(T, _)` are
  always true).
- The type checker infers the hole's type from the function body and emits
  a `:type_hole_inferred` pipeline event with the inferred type.

### Phase 4: LSP incremental compilation

Performance optimization for large projects.

- **Version-based AST cache** -- on `textDocument/didChange`, re-parse and
  re-diagnostics are skipped when the incoming document version matches
  the cached entry, avoiding redundant work during rapid edits.

### Phase 5: Cross-module protocol dispatch

Complete the protocol story.

- **Registry-aware call resolution** -- when the codegen encounters an
  unresolved function call, it queries the global protocol registry;
  matching methods emit remote calls to the providing module.
- **Runtime fallback** -- calls not found in the registry fall back to
  local call resolution, allowing graceful degradation when compilation
  order does not guarantee visibility.

### Phase 6: Testing infrastructure

First-class testing support.

- `cure test` discovers `.cure` test files in `test/`, compiles each file,
  runs all `test_*` functions, and reports per-test pass/fail counts.
- `Std.Test` with `assert`, `assert_eq`, `assert_ne`, `assert_gt`,
  `assert_lt` assertion primitives.
- **670 tests.** Zero Credo issues. Zero compilation warnings. 49 Elixir
  source files. 18 stdlib modules.

## Implemented: v0.15.0

Effect system, documentation generator, developer experience improvements,
and full record type support with functional update syntax.

### Phase 1: Effect system

Track side effects in the type system. Pure functions can be aggressively
optimized; effectful functions are clearly marked.

- **Effect-annotated function types** -- `{:effun, params, ret, effects}`
  type with `MapSet` of effect kinds: `:io`, `:state`, `:exception`,
  `:spawn`, `:extern`.
- **Syntax: `! Effect`** -- optional effect annotations after return types:
  `fn read(path: String) -> String ! Io`. Inferred by default.
- **Effect inference** -- `Cure.Types.Effects` module walks function bodies,
  classifies effects from `@extern` targets, keywords (`send`, `spawn`,
  `throw`, `receive`), and known stdlib functions. Transitive propagation.
- **Effect subtyping** -- pure functions are subtypes of effectful functions
  with the same signature. Effect sets follow subset ordering.
- **Optimizer integration** -- `Inline` pass uses effect-grounded purity
  check instead of ad-hoc function name lists.
- **LSP hover** -- shows inferred effects alongside function signatures.
- **Pipeline events** -- `{:type_checker, :effects_inferred, ...}` and
  `{:type_checker, :effect_error, ...}` events.

### Phase 2: Documentation generator

Extract function signatures, type annotations, and doc comments into
browsable HTML documentation.

- **`##` doc comments** -- lexer emits `:doc_comment` tokens for double-hash
  lines; parser attaches them as `:doc` metadata on definitions.
- **`Cure.Doc.Extractor`** -- extracts structured doc maps from module ASTs:
  module name, module doc, functions with signatures/docs/effects, protocols,
  types.
- **`Cure.Doc.HTMLGenerator`** -- renders standalone HTML pages with
  syntax-highlighted signatures, effect badges, dark/light mode CSS.
- **`cure doc`** -- CLI subcommand generates HTML docs for `.cure` files.
- **Stdlib documented** -- all 18 stdlib modules annotated with `##` doc
  comments.

### Phase 3: Developer experience

- **`cure repl`** -- minimal interactive session backed by `compile_and_load`.
- **`cure fmt`** -- source formatter using `Cure.Compiler.Printer`.
- **Unused variable tracking** -- `Env` tracks variable usage; foundation for
  E007 warnings.
- **Error catalog E006-E010** -- Effect Violation, Unused Variable,
  Undocumented Public Function, Unreachable Clause, Missing Effect Annotation.

### Phase 4: Records

Full record type support: definitions, typed field access, and functional
update syntax.

- **Named type representation** -- `Type.resolve/1` now returns
  `{:named, "TypeName"}` for user-defined record/ADT names instead of `:any`.
  This carries the name through the type checker so field schemas are
  accessible during inference.
- **Field schema registration** -- the checker's first pass registers each
  `rec` definition's field types in `Env.types`. Field access `p.x` on a
  `Point`-typed value infers the declared field type (`Int`) rather than `Any`.
- **Record construction typing** -- `Point{x: 1, y: 2}` infers type
  `{:named, "Point"}` and the codegen emits a BEAM map literal with a
  `__struct__` key.
- **Record update syntax** -- `TypeName{base | field: val, ...}` produces a
  modified copy. Only listed fields change; all others are preserved.
  Compiles to the BEAM map-update instruction (`Map#{key := val}`).
  The parser detects update vs. construction by probing for `|` after the
  first sub-expression, rewinding if not found.
- **Type checker integration** -- override field values are checked against
  the registered schema. Wrong field types produce a compile-time error.
- **678 tests.** Zero Credo issues. Zero compilation warnings. 54 Elixir
  source files.

## Implemented: v0.16.0

Finitomata-inspired FSM rewrite. FSM definition and transition logic now
coexist in the same `.cure` file via callback mode; simple mode stays
backward-compatible.

### Dual-mode compilation

- **Callback mode** -- FSMs with an `on_transition` block compile to
  `GenServer`-based modules with embedded transition tables, user-defined
  `on_transition/4` dispatch, and lifecycle callbacks.
- **Simple mode** (backward-compatible) -- `gen_statem` codegen now
  includes `transitions/0` and `allowed/2` introspection, hard-event
  auto-fire via `next_event` actions, and soft-event silent catch-all
  clauses.
- `Cure.Compiler` pipeline handles both modes transparently.

### Event suffixes and lifecycle callbacks

- **Hard events** `event!` auto-fire when the FSM enters a state where the
  event is the sole outgoing transition. The compiler verifies the
  constraint.
- **Soft events** `event?` silently swallow failed transitions without
  logging or calling `on_failure`.
- `on_enter`, `on_exit`, `on_failure`, and `on_timer` lifecycle callbacks.
- `@timer <ms>` annotation for periodic `on_timer` invocations.

### Introspection and tooling

- `transitions/0`, `allowed/2`, `allowed?/2`, `responds?/2` --
  runtime-introspectable FSM API; `Cure.FSM.Runtime.allowed?/3` and
  `responds?/3` delegation.
- LSP: FSM transitions as children in the symbol tree with event-suffix
  labels; lifecycle callbacks in hover; FSM callback completions inside
  FSM blocks.
- MCP: `analyze_fsm` reports compilation mode, timer, event kinds with
  suffixes, and callback blocks.
- Printer emits event suffixes and `@timer` annotations.
- `examples/cure_turnstile/` rewritten to use callback mode.

## Implemented: v0.17.0 -- Proofs & Polish

The dependent-typing core grows up; the everyday UX catches up. Three
themes land together: dependent-type maturation, friction-free UX, and
ecosystem groundwork.

### Dependent-type maturation

- **Sigma types** `Sigma(name: T1, T2)` -- dependent pairs with
  componentwise subtyping; round-trip to plain runtime tuples.
- **Pi types** -- dependent function types with `:explicit`, `:implicit`,
  and `:erased` parameter modes and AST-based return types.
- **`Cure.Types.Reduce`** -- terminating normaliser for type-level
  arithmetic, booleans, comparisons, and pair projection. Trivial
  arithmetic never touches the SMT solver.
- **Propositional equality** `Eq(T, a, b)` with constructor `refl` and
  eliminator `rewrite`; runtime-erased via `:cure_refl`.
- **`Cure.Types.Unify`** -- first-order unification with occurs check
  for implicit-argument inference; `:unification_trace` pipeline event
  rendered in LSP hover and CLI error output.
- **`Cure.Types.Holes`** -- `?name` and `??` placeholders with goal-type
  and local-context reporting via `:hole_goal`.
- **`Cure.Types.Totality`** -- coverage + structural-recursion analysis;
  `:total | :partial | :unknown` classification; `#[total]` decorator.
- **`Cure.Types.PathRefinement`** -- path-sensitive refinement flow along
  `if` / `match` guards.
- `Std.Equal` -- `refl`, `sym`, `trans`, `cong`.
- `Std.Refine` -- `NonZero`, `Positive`, `Negative`, `NonNegative`,
  `Percentage`, `Probability`, and predicate helpers.

### Friction-free UX

- **`Cure.REPL`** -- full rewrite. Multi-line input, meta-commands `:t`,
  `:doc`, `:effects`, `:load`, `:reload`, `:use`, `:holes`, `:env`,
  `:reset`, `:fmt`, `:help`, `:quit`. History persisted to
  `~/.cure_history`.
- **`Cure.Watch`** -- `cure watch` recompiles, type-checks, or runs tests
  on every save with a 200 ms debounce.
- **`Cure.LSP.Server`** -- inlay hints, signature help, formatting,
  `prepareRename` / rename, code lenses, semantic tokens, workspace
  symbols.
- Error catalog codes `E011`-`E020` covering implicit-argument failures,
  sigma destructuring, totality, unfilled holes, refinement
  counterexamples, dependent-type mismatches, equality-proof mismatches,
  and doctests.
- `cure new <name> [--lib | --app | --fsm]` with three templates.
- `Cure.lock` lockfile; `cure deps update`, `cure deps tree`; git-based
  dependency resolution in `Cure.Project.resolve_git_dep/2`.
- `cure bench` -- benchmark runner for `bench/**/*.cure`.
- `cure test --filter PATTERN --doctests`; `Cure.Doc.Doctests` harvests
  `cure>` / `=>` doctests from `##` blocks.

### Ecosystem groundwork

- MIT `LICENSE` at repo root.
- Complete `mix.exs` `package` block for Hex publication, including docs
  extras.
- `vscode-cure/` -- TypeScript / LSP VS Code extension scaffold with
  TextMate grammar and language configuration.
- `docs/PACKAGE_REGISTRY.md` -- design document for the v0.18.0+
  package registry.
- `docs/TUTORIAL.md` -- ten progressive chapters.
- `docs/DEPENDENT_TYPES.md` -- full guide for the new type-system
  features.

### Numbers

- ~11 new Elixir modules, ~12 new test files, ~155 new tests (830
  total, 0 failures). Zero credo issues in strict mode.
- 2 new stdlib `.cure` modules (`Std.Equal`, `Std.Refine`); 20 total.
- 7 new examples, one for each major feature.
- `mix check` runs 20 stdlib + 24 example regressions in CI.

## Future

These are not scheduled but are on the long-term radar.

**Type optimizer.** Monomorphization: when a polymorphic function is only
called with concrete types, generate specialized versions. Profile-guided
optimization (PGO): use profiler data to prioritize hot paths for
specialization.

**Broader IDE support.** VS Code extension with syntax highlighting, snippet
templates, and integrated diagnostics. Helix and Zed configurations.

**Hex.pm integration.** Publish Cure packages to Hex.pm alongside Elixir
and Erlang packages. A Cure package would include compiled `.beam` files and
a `Cure.toml` manifest.

**REPL (advanced).** Stateful REPL with incremental compilation and
persistent environment across expressions.
