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
- `docs/PACKAGE_REGISTRY.md` -- design document for the v0.19.0+
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

## Implemented: v0.18.0 -- Deep Destructuring

`match` and `let` grow up. Pattern matching now descends through
arbitrary nesting across tuples, lists (cons and fixed), maps,
records, and ADT constructors. The previous implementation quietly
miscompiled map patterns (wrong Erlang abstract form) and never
recursed into nested shapes; v0.18.0 replaces it wholesale.

### Pattern engine

- **`Cure.Compiler.PatternCompiler`** -- dedicated pattern-to-Erlang
  translator, separated from expression codegen. Every pattern node
  is dispatched through a single recursive entry point.
- Map patterns emit `map_field_exact` (`:=`), not `map_field_assoc`
  (`=>`). Matching against a map pattern actually matches now.
- Record patterns lower to map patterns with
  `__struct__ := :tag` and per-field exact entries; unspecified
  fields are open-matched.
- Field punning: `Point{x, y}` is shorthand for `Point{x: x, y: y}`.
- Pin operator `^x` compares against a previously-bound value; the
  compiler lowers it to a synthetic `andalso` equality guard.
- Repeated variable occurrences in the same pattern emit equality
  guards too: `%[x, x]` matches only when both slots are equal.
- ADT constructors, cons, and tuple patterns recurse correctly
  through nested sub-patterns.

### Type checker

- `bind_pattern_vars/3` rewritten with deep recursion. Tuple
  patterns narrow element-by-element; map and record patterns
  resolve per-field through the record schema or the map value
  type.
- Maranget-style nested-exhaustiveness pass in
  `Cure.Types.PatternChecker.check_nested/2` reports concrete
  missing witnesses (for example ``"%[Error(_)]"``) under code
  `E025`. The flat classifier from v0.11.0 remains as a fast path.
- New error codes `E021`-`E025` (unknown record field, record-field
  type mismatch, non-literal map-pattern key, unbound pin, nested
  non-exhaustive match).

### Parser

- `^` lexed as `:caret`; parser now produces
  `{:pin, meta, [inner]}` for the pin operator.
- Field-punning in record patterns and map pairs: a bare identifier
  followed by `,` or `}` desugars to `name: name`.

### Standard library and examples

- New **`Std.Match`** module -- eight destructuring helpers
  (`unpack_pair/1`, `fst/1`, `snd/1`, `head_tail/2`, `uncons/1`,
  `first_two/2`, `unwrap_ok/2`, `unwrap_some/2`).
- `Std.List.uncons/1`, `Std.List.split_first/2` added using cons
  destructuring.
- `examples/destructuring.cure`, `examples/json_tree.cure` --
  end-to-end showcases. `examples/pattern_guards.cure` extended
  with record patterns, field-punning, and nested ADT destructuring.

### Documentation

- `docs/PATTERNS.md` -- authoritative pattern matching reference
  (Cure surface syntax, Erlang abstract-form mapping, binding
  semantics, exhaustiveness behaviour).
- `docs/LANGUAGE_SPEC.md` pattern-matching section rewritten from a
  12-line stub to a full reference.
- `docs/TUTORIAL.md` -- new Chapter 4 "Destructuring in `match`";
  later chapters renumbered.

### Numbers

- 1 new Elixir module (`Cure.Compiler.PatternCompiler`, ~480 LOC);
  rewrites inside `Codegen`, `Checker`, and `PatternChecker`.
- 1 new stdlib module (`Std.Match`), 1 extended (`Std.List`);
  21 stdlib modules total.
- 2 new examples, 1 extended.
- 923 tests passing (3 doctests, 920 tests) -- 26 new, 0 regressions.
- `mix credo --strict`: 0 issues across 117 source files.
- `mix cure.check.stdlib`: 21/21 clean;
  `mix cure.check.examples`: 26/26 clean.

## Implemented: v0.19.0 -- Bring the Furniture

Ergonomics, proofs, and the first half of a registry.

### Language additions

- **`proof` containers** -- new `proof Name.Path` keyword; every
  binding inside must return `Eq(T, a, b)` or a refinement witness.
  Enforced as `E026`.
- **`assert_type expr : T`** -- compile-time type assertion that is
  stripped at codegen. Mismatches surface as `E027`.
- **Record field defaults** -- `rec Person\n  name: String = ""` --
  construction merges declared defaults with user-supplied fields;
  default/declared mismatches emit `E028`.
- **`@derive(Show, Eq, Ord)`** wired end-to-end on `rec` through
  `Cure.Types.Derive` plus the codegen's expansion pass.
- **Multi-head cons patterns** `[a, b, c | rest]` desugar to
  right-associated cons cells.

### Standard library additions

- **`Std.Proof`** -- reflexivity laws (`plus_zero`, `zero_plus`,
  `plus_comm`, `append_nil`, `map_id`).
- **`Std.Gen`** -- tiny stateless generator API (`int_in`, `bool`,
  `one_of`, `list_int`, `list_of_int`) backed by `:rand`.
- **`Std.Iter`** -- lazy iterator protocol; constructors `empty`,
  `from_list`, `range`; consumers `fold`, `take`, `to_list`.
- **`Std.Test.forall/3`** -- property-based runner.

### Totality

- `Cure.Types.Totality.check_mutual/1` -- Tarjan SCC analysis; cycles
  without a structural-decrease proof raise `E029`.

### Packaging

- `Cure.Project.Version` -- SemVer + constraint parser (`~>`, `>=`,
  `<=`, `<`, `>`, `==`, compound `and`); MAJOR.MINOR is shorthand for
  MAJOR.MINOR.0.
- `Cure.Project.Resolver` -- deterministic backtracking resolver
  over a local workspace; conflicts surface as `E030`. Remote index
  service deferred to v0.20.0.

### Error catalog

Five new codes `E026`-`E030`.

### Numbers

- 2 new Elixir modules (`Cure.Project.Version`, `Cure.Project.Resolver`);
  major extensions to `Totality`, `Derive`, `Codegen`, `Parser`,
  `Checker`, and `Type`.
- 3 new stdlib modules (`Std.Proof`, `Std.Gen`, `Std.Iter`); 24
  total.
- 4 new examples, 1 new doc (`PROOFS.md`).
- ~970 tests (up from 923); `mix credo --strict`: 0 issues;
  `mix cure.check.stdlib`: 24/24; `mix cure.check.examples`: 30/30.

## Implemented: v0.20.0 -- The Shape of Things

AST polish across four coupled compiler features. Plain `#`
comments are first-class nodes in the tree, binary literals and
patterns gain the full Elixir-style segment grammar
(`<<x::utf8, rest::binary>>`), a Wadler/`Inspect.Algebra`-style
pretty-printer lands behind `cure fmt --algebra`, and pattern
narrowing can expose disjoint-tag and literal-equality witnesses
via `Cure.Types.PatternRefinement`. None of the four tracks are
new surface-language features on their own -- they are the
scaffolding the next generation of features (binary destructuring,
width-aware layout, path-sensitive dependent narrowing) will build
on.

### Plain comment AST nodes

- `Cure.Compiler.Lexer.tokenize/2` gains a
  `preserve_comments: true` option. Plain `#` comments are emitted
  as `:line_comment` tokens; doc comments (`##`, `###`) continue
  to be preserved regardless.
- `Cure.Compiler.Parser` threads those tokens into the AST as
  `{:comment, [line:, col:], text}` nodes in top-level programs,
  container bodies, and block bodies. Indented comment-only lines
  preceding a block's `:indent` are routed inside the block so the
  comment ends up a sibling of the definition it documents.
- `Cure.Compiler.Codegen` and `Cure.Types.Checker` skip comment
  nodes silently so comment preservation has no runtime or
  type-checking cost.

### Full bitstring segments

- `:colon_colon` lexer token for `::`, distinct from `:colon`
  (type annotations) and `:atom` (symbol literals).
- `Cure.Compiler.Parser.parse_binary_literal/1` now wraps every
  element of `<<...>>` in a `{:bin_segment, meta, [value]}` node.
  Meta keys: `:type` (`:integer`, `:float`, `:bits`, `:bitstring`,
  `:bytes`, `:binary`, `:utf8`, `:utf16`, `:utf32`),
  `:signedness`, `:endianness`, `:size` (an AST node), `:unit`
  (integer). Specifiers chain with `-`
  (`::binary-size(n)`); a bare integer is shorthand for
  `size(n)`. Defaults mirror Erlang:
  `integer-unsigned-big-size(8)-unit(1)`, with `utf8` / `utf16` /
  `utf32` providing their own implicit size.
- `Cure.Compiler.Codegen` and `Cure.Compiler.PatternCompiler`
  translate the segment AST into full Erlang `:bin_element` forms
  in both construction and pattern positions.
- `Cure.Compiler.Printer` round-trips segments back into surface
  syntax.

This is the groundwork for the v0.21.0 headline feature: full
Erlang-style destructuring of binaries in `match`, function heads,
`let`, and comprehension generators.

### Algebra-based formatter

- `Cure.Compiler.Algebra` -- a new `Inspect.Algebra`-style document
  module with `empty`, `concat`, `nest`, `break`, `line`, `group`,
  `string`, `space`, `fold`, and a best-fit `format/2`. A `group`
  fits flat when its content stays within the remaining width;
  otherwise every soft break inside renders as a newline at the
  current indent.
- `Cure.Compiler.AlgebraFormatter` -- AST-to-document renderer
  that walks top-level programs, containers, and blocks, and
  delegates per-node rendering to the existing `Printer`.
  Standalone `{:comment, ...}` nodes round-trip as `# <text>`
  lines; sequences are separated by blank lines.
- `Cure.Compiler.Formatter.format_algebra/2` runs the new
  formatter with comment-aware round-trip verification: the
  formatted buffer must re-parse to an AST structurally equal to
  the input (modulo comment placement and position metadata),
  otherwise the original source is returned unchanged.
- CLI: `cure fmt --algebra` opts in. The existing byte-level safe
  formatter stays the default for v0.20.0 and will be promoted to
  `--algebra` as the default in v0.21.0.

### Structural refinement narrowing

- `Cure.Types.PatternRefinement.narrow/2` returns
  `{bindings, narrowed_scrutinee}` for any pattern against any
  scrutinee type. Literal sub-patterns yield equality refinements
  (`{x: Int | x == 0}` for `0`); constructor patterns (`Ok(v)`,
  `Error(e)`) and map patterns with a literal `:kind` tag yield
  `{:variant, tag, args}` witnesses. Integrates with the existing
  `Cure.Types.Refinement` SMT representation, so every narrowed
  type is something the SMT translator already understands.
- `bind_pattern_vars/3` in `Cure.Types.Checker` keeps its existing
  precise element typing for tuples / lists / records / maps;
  `PatternRefinement` is exposed as a separate module for callers
  that want the narrowed scrutinee. v0.21.0 will route
  `do_infer({:pattern_match, ...})` through it so match-arm bodies
  take advantage of the narrowing, and the path-sensitive
  refinement pass can propagate disjoint-tag witnesses across
  subsequent expressions in the same branch.

### Numbers

- 3 new Elixir modules (`Cure.Compiler.Algebra`,
  `Cure.Compiler.AlgebraFormatter`,
  `Cure.Types.PatternRefinement`); major extensions to
  `Cure.Compiler.Lexer`, `Cure.Compiler.Parser`,
  `Cure.Compiler.Codegen`, `Cure.Compiler.PatternCompiler`,
  `Cure.Compiler.Printer`, `Cure.Compiler.Formatter`,
  `Cure.Types.Checker`, and the CLI.
- 1016 tests pass (up from 970); `mix credo --strict`: 0 issues
  across 136 files; `mix cure.check.stdlib`: 24/24;
  `mix cure.check.examples`: 30/30.

### Deferred to v0.21.0

Type-checker refinement narrowing *through* binary patterns
(propagating `size(n)` into refinements on `rest`). Exhaustiveness
analysis for binary patterns (`Cure.Types.PatternChecker`).
Promotion of `cure fmt --algebra` to the default formatter.
Type-directed `@derive` extensions (Functor, Monoid, JSON). Full
Erlang-style destructuring of binaries in `match` expressions,
function heads, `let` bindings, and comprehension generators --
the segment AST from v0.20.0 is the groundwork; v0.21.0 adds
type-checker narrowing across binary segments and the
exhaustiveness analysis that goes with it.

Three parser/type gaps surfaced during the v0.20.0 cycle also
roll into v0.21.0: ADT constructor payloads must accept arbitrary
type expressions (including function arrows, so
`type Callback = On((Int) -> Int) | Off` parses and type-checks);
multi-line `type` ADT declarations with leading `|` on
continuation lines must parse (the indented layout currently
defeats `parse_type_def`); and `let` must support in-place
destructuring with the same depth and exhaustiveness guarantees
as `match` arms (ADT constructors, tuples, lists, records, and
maps, with `E025` on non-exhaustive bindings).

### Deferred to v0.22.0

Multi-statement lambda bodies -- brace-delimited
(`fn (x) -> { stmt1; stmt2; final }`) and `end`-terminated
(`fn (x) ->\n  stmt1\n  stmt2\nend`) block forms for anonymous
functions embedded in argument lists where the existing
indented-block form is not usable.
### Deferred to v0.23.0

Remote package-registry index service, publication signing, and
Hex.pm cross-publishing -- a `Cure.Project.Registry` HTTP client
against a read-only index protocol, Ed25519 archive signing, and
a `cure publish --hex` export path.

## Implemented: v0.21.0 -- Through the Segments

The v0.21.0 release turns the v0.20.0 AST scaffolding into
user-visible features and clears three language gaps that surfaced
during the v0.20.0 cycle. The headline is full Erlang-style
destructuring of binaries in `match`, multi-clause function heads,
and `let` bindings, with a dedicated exhaustiveness pass that
surfaces under code `E031`.

### Binary destructuring

- `Cure.Types.Checker.bind_pattern_vars/3` grows a `:bin_segment`
  clause. Every `<<...>>` pattern in `match`, function heads, and
  `let` introduces its inner variables with the type implied by the
  segment specifier: `integer`/`size(n)` -> `Int`, `float` ->
  `Float`, `utf8`/`utf16`/`utf32` -> `Char`,
  `binary`/`bytes`/`bitstring`/`bits` -> `Bitstring`.
- `Cure.Types.PatternChecker.check_binary_exhaustiveness/2` --
  dedicated Maranget-lite coverage analysis over a sequence of
  binary-pattern arms. A top-level wildcard, or the combination of
  an empty-binary arm and an open-ended tail arm, covers the
  scrutinee; otherwise a concrete witness (`"<<>>"` or
  `"<<_, _rest::binary>>"`) is reported under code `E031`.
- `Cure.Types.PatternRefinement.narrow/2` gets a binary-literal
  branch that narrows the scrutinee through the segments.

### In-place `let` destructuring

- `let` bindings reuse the v0.18.0 deep-destructuring engine.
  `let Ok(x) = expr`, `let %[a, b] = pair`, `let [h | t] = xs`,
  `let Point{x, y} = p`, and `let <<tag, _::binary>> = buf` all
  bind the right variables with the right narrowed types.
- Non-exhaustive `let` patterns emit code `E034` as a warning;
  the binding still compiles, and Erlang's `=` raises at runtime
  on a failed match.

### Multi-line `type` ADT declarations

- `parse_type_def/1` absorbs an optional wrapping `:indent`/`:dedent`
  pair, accepts an optional leading `|` before the first variant,
  and `parse_more_variants/1` skips newlines before peeking for
  `|`. Both layouts parse identically to the single-line form:

```cure
type Shape =
  | Circle(Int)
  | Square(Int)
  | Triangle(Int, Int, Int)
```

- `E033` Multi-line Type Layout Invalid added to the error catalog.

### ADT function-type payloads

Constructor payloads accept arbitrary type expressions including
function arrows. `type Callback = On(Int -> Int) | Off` and
`type Transform = Morph((Int, Int) -> Int) | Id` compile end-to-end;
pattern matching binds the callable to a variable callable from
inside the arm.

### Algebra formatter as default

`cure fmt` now runs the Wadler/`Inspect.Algebra`-style pretty
printer by default. The legacy byte-level formatter remains
available via `cure fmt --safe`; `cure fmt --check` routes through
the algebra formatter so CI agrees with interactive use.

### `@derive(Functor, Monoid, JSON)`

`Cure.Types.Derive.derive/3` gains three new targets: `:functor`
emits `fmap(x, f)` that applies `f` to every field; `:monoid`
emits `combine(a, b)` that pairwise combines each field with `<>`;
`:json` emits `to_json(x)` that renders the record as a JSON
object whose keys are the field names. `can_derive?/1` is extended
accordingly.

### Multi-clause parameter destructuring

`check_multi_clause/7` routes every clause parameter through
`bind_pattern_vars/3` instead of only binding bare variables. ADT
constructors, tuples, cons patterns, record patterns, and binary
patterns in function heads now introduce their inner variables for
the clause body.

### Error catalog

Four new codes `E031`-`E034` (Binary Pattern Not Exhaustive,
Function Type Payload Invalid, Multi-line Type Layout Invalid, Let
Pattern Not Exhaustive) with examples and fix guidance.

### Numbers

- 1078 tests pass (up from 1050, 3 doctests + 1075 tests);
  `mix credo --strict`: 0 issues across 137 source files;
  `mix cure.check.stdlib`: 25/25; `mix cure.check.examples`: 40/40.
- 5 new examples (`binary_destructuring.cure`, `adt_fn_payload.cure`,
  `multi_line_adt.cure`, `let_destructuring.cure`,
  `json_derive.cure`); 1 new doc (`docs/BINARIES.md`); updates to
  `docs/LANGUAGE_SPEC.md` and `docs/TUTORIAL.md` (new Chapter 11
  "Binary parsing").

## Implemented: v0.22.0 -- Loose Ends
v0.22.0 closes the three language-surface gaps that v0.20.0 /
v0.21.0 deliberately left open: multi-statement lambda bodies,
binary comprehension generators, and full byte-size refinement
propagation through `rest::binary` tails. The v0.21.0 "Unreleased"
first-class FSM overhaul also graduates into a shipped release.
### Multi-statement lambda bodies
- `Cure.Compiler.Parser.parse_lambda_body/2` routes the body
  through a new `parse_lambda_block_body/2` dispatcher. Indented
  and single-expression bodies keep their v0.19.0 semantics; two
  new shapes land for argument positions where the lexer
  suppresses newlines:
```cure
map(xs, fn(x) -> { let y = x + 1; y + 2 })
map(xs, fn(x) -> let y = x + 1; y + 2; end)
```
- Both shapes emit `{:block, [block_shape: :brace | :end, ...], exprs}`,
  reusing the existing codegen and checker paths. The Printer and
  algebra formatter round-trip the author's chosen shape.
- `end` is now a reserved keyword. Cure's stdlib and example
  programs do not use it as an identifier; third-party code that
  does must rename.
### Binary comprehension generators
- `parse_generator_or_filter/1` dispatches on `:binary_open` and
  delegates to `parse_binary_generator/1`. Segments inside the
  generator are parsed at binding power 42 so the trailing `<-`
  arrow is not mis-tokenised as a less-than comparison.
- `Cure.Compiler.Codegen.compile_comprehension/3` lowers the new
  `:binary_generator` qualifier to Erlang's `b_generate` form
  inside the existing `:lc` comprehension:
```cure
[byte for <<byte <- "abc">>]       # [97, 98, 99]
[word for <<word::16 <- buf>>]     # 16-bit words
[ch   for <<ch::utf8 <- text>>]    # UTF-8 code points
```
- `Cure.Types.Checker.do_infer/2` on `:comprehension` now binds
  every qualifier's pattern variables into the body's environment
  via `bind_pattern_vars/3`.
### `byte_size` arithmetic refinements
- `Cure.SMT.Translator` speaks `byte_size/1` as an uninterpreted
  `(Int) -> Int` function. Queries that reference `byte_size`
  prepend `(declare-fun byte_size (Int) Int)` and switch to the
  `QF_UFLIA` logic automatically.
- `Cure.Types.PatternRefinement.narrow/2` rewrites its binary-
  segment branch. Trailing `rest::binary`/`rest::bytes`/
  `rest::bitstring` tails receive
  `{rest: Bitstring | byte_size(rest) == byte_size(scrutinee) - sum}`
  where the sum is the byte-aligned count of preceding segments.
  When a segment's size cannot be linearised the tail degrades to
  plain `Bitstring` and the pipeline emits a `:refinement_ignored`
  event under code `E037`.
### Error catalog
Three new codes `E035`-`E037` (Lambda Block Unterminated, Binary
Comprehension Source Not Bitstring, Binary Segment Size Non-Linear).
### First-class FSM handling
The v0.21.0 "Unreleased" block that described the `%Cure.FSM.State{}`
rewrite of callback-mode FSMs is promoted to a shipped surface.
`start_link/1` accepts three init shapes, `on_transition` clauses
receive the struct as their 4th argument, and `@notify_transitions`
/ `@initial` / `@auto_caller` annotations carry first-class payload
semantics. Simple-mode (`gen_statem`) FSMs are entirely unchanged.
### Numbers
- 1114 tests pass (up from 1078; 3 doctests + 1111 tests);
  `mix credo --strict`: 0 issues across 142 source files;
  `mix cure.check.stdlib`: 25/25; `mix cure.check.examples`:
  44/44 (up from 40/40).
- 3 new example files (`lambda_block.cure`,
  `binary_comprehension.cure`, `byte_size_refinement.cure`).
### Deferred to v0.23.0
Remote package-registry index service, publication signing, and
Hex.pm cross-publishing -- the `Cure.Project.Registry` HTTP
client against the read-only index protocol, Ed25519 archive
signing, and the `cure publish --hex` export path are all
rescheduled for v0.23.0.

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
