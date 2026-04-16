# Changelog

All notable changes to Cure are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [Unreleased]

---

## [0.16.0] -- Finitomata-Inspired FSM Rewrite

Complete rethinking of FSM handling. The FSM definition and transition logic
now coexist in the same `.cure` file via callback mode, inspired by
[Finitomata](https://hexdocs.pm/finitomata). Simple mode remains
backward-compatible.

### Added -- Dual-Mode FSM Compilation
- **Callback mode**: FSMs with an `on_transition` block compile to
  `GenServer`-based modules with embedded transition tables, user-defined
  `on_transition/4` dispatch, and lifecycle callbacks
- **Simple mode** (backward-compatible): `gen_statem` codegen now includes
  `transitions/0` and `allowed/2` introspection, hard event auto-fire via
  `next_event` actions, and soft event silent catch-all clauses
- `Cure.Compiler` pipeline handles both modes transparently

### Added -- Event Suffixes
- **Hard events** (`event!`): auto-fire when the FSM enters a state where
  the event is the sole outgoing transition. Compiler verifies this constraint.
- **Soft events** (`event?`): failed transitions are silently swallowed
  without logging or calling `on_failure`

### Added -- Lifecycle Callbacks
- `on_enter` -- called after entering a state
- `on_exit` -- called before leaving a state
- `on_failure` -- called when a normal (non-soft) transition fails
- `on_timer` -- called periodically when `@timer <ms>` is set

### Added -- FSM Callback Clause Syntax
- Parser: `(pat1, pat2, ...) -> body` clause syntax for FSM callbacks
- Lexer: `fsm_transition_depth` tracking for `!`/`?` identifier suffixes
- Parser: `@timer <ms>` annotation support
- Parser: `event_kind` classification (`:hard`, `:soft`, `:normal`)

### Added -- Verifier Enhancements
- Hard event validation: `!` events must be the sole outgoing event
- `on_transition` coverage warnings for ambiguous transitions
- Informational pipeline events for coverage analysis

### Added -- Introspection API
- `transitions/0` -- compiled transition table (both modes)
- `allowed/2` / `allowed?/2` -- check transition validity
- `responds?/2` -- check event availability from a state (callback mode)
- `Cure.FSM.Runtime.allowed?/3` and `responds?/3` delegation

### Changed -- LSP
- Symbols: FSM transitions as children with event suffix and kind labels;
  callback blocks and `@timer` as FSM children; detail shows compilation mode
- Hover: `on_transition` and lifecycle callbacks show signature documentation;
  hard/soft event patterns show explanatory hover text
- Completions: FSM callback names offered inside FSM blocks

### Changed -- MCP
- `analyze_fsm`: reports compilation mode, timer, event kinds with suffixes,
  and callback blocks with clause counts
- `syntax_help("fsm")`: documents both modes, event suffixes, lifecycle callbacks

### Changed -- Printer
- Event suffix output (`!`/`?`) in transition rendering
- Callback block rendering in FSM output
- `@timer` annotation rendering

### Changed -- Examples
- `cure_turnstile/` rewritten to use callback mode with `on_transition`

---

## [0.15.0] -- Developer Experience

Public API for parsing and printing Cure source, an effect system for tracking
side effects through the type system, HTML documentation generation, a code
formatter, and an interactive REPL.

### Added -- Public API
- `Cure.quote/2` -- parse Cure source into MetaAST 3-tuples
- `Cure.quoted_to_string/2` -- convert MetaAST back to Cure source (round-trip capable)
- Clean entry point for tooling, macros, and metaprogramming

### Added -- Effect System
- `Cure.Types.Effects` -- infer side effects from function bodies
- Effect kinds: `:io`, `:state`, `:exception`, `:spawn`, `:extern`
- Effect checking: declared effects validated against inferred effects
- `@extern` classification by target module (`:io` -> IO, `:ets` -> state, etc.)
- Pipeline event emission (`:effects_inferred`) for effect inference results
- Pure functions identified for aggressive optimization

### Added -- Source Printer
- `Cure.Compiler.Printer` -- full AST-to-source printer covering all Cure constructs
- Handles literals, operators, bindings, conditionals, pattern matching, collections,
  comprehensions, lambdas, function definitions, containers (mod/rec/enum/proto/impl/fsm),
  type annotations, decorators, imports, exception handling
- Round-trip verified: `quote -> print -> re-quote` produces equivalent AST

### Added -- Documentation Generator
- `Cure.Doc.Extractor` -- extract structured documentation from module ASTs
  (functions, protocols, types, effects, visibility, guards, clauses)
- `Cure.Doc.HTMLGenerator` -- static HTML docs with dark/light theme (system preference),
  per-module pages, function signature rendering, effect badges
- `cure doc [path|dir]` CLI command

### Added -- Code Formatter
- `cure fmt [path|dir]` -- format `.cure` source files via parse-then-print
- Consistent indentation and style across projects

### Added -- Interactive REPL
- `cure repl` -- evaluate Cure expressions interactively
- Wraps input in temporary modules, compiles and executes on the fly

### Added -- Compiler Refactoring
- `Cure.Compiler.Token` -- extracted Token struct with type, value, line, col
- `Cure.Compiler.Parser.Precedence` -- extracted Pratt parser binding power table
  with operator category and symbol lookup

### Added -- Stdlib
- `Std.Test` (5 fns) -- assert, assert_eq, assert_ne, assert_gt, assert_lt
- Total: 18 stdlib modules

### Added -- Examples
- `dependent_types.cure` -- refinement types and guarded functions (12 examples total)

---

## [0.14.0] -- Real-World Readiness

A language is real-world ready when programs can have dependencies, protocols
work across module boundaries, and tests can be written in the language itself.

### Added -- Package Management (Phase 1)
- `Cure.Project` -- Cure.toml project file parsing (minimal TOML subset)
- `Cure.Project.resolve_deps/1` -- compile path-based dependencies, add to code path
- `Cure.Project.init/1` -- scaffold new projects with Cure.toml, lib/, test/
- `Cure.Project.compiler_opts/1` -- read compiler options from project config
- `cure init <name>` CLI command
- `cure deps` CLI command

### Added -- Cross-Module Protocol Dispatch (Phase 5)
- `Cure.Types.ProtocolRegistry` -- ETS-backed global protocol implementation registry
- `register_impl/4`, `lookup_impl/3`, `has_impl?/2`, `list_impls/1` APIs
- `list_impls_by_method/1` -- cross-protocol method lookup
- Started automatically in `Cure.Application`
- Used by codegen for cross-module protocol dispatch

### Added -- Testing Infrastructure (Phase 6)
- `cure test` CLI command -- compile and run `.cure` test files from test/
- Discovers functions starting with `test`, reports pass/fail counts
- `Std.Test` stdlib module -- assert, assert_eq, assert_ne, assert_gt, assert_lt

---

## [0.13.0] -- Depth Over Breadth

Deepened every subsystem from "working foundation" to "production ready."
Closed remaining gaps with the legacy Erlang implementation (~17,000 lines
ported, primarily the type optimizer and 5 LSP modules).

### Added -- Dependent Type Verification (Phase 1)
- Constrained function signatures stored in type env
- Call-site verification via SMT (`Cure.SMT.Solver.prove_implication/4`)
- Counterexample extraction from Z3 models via `Cure.SMT.Parser.parse_model/1`
- Type-level arithmetic in return types (`Vector(T, m + n)`)
- Value parameter parsing: `fn f(v: Vector(T, n: Nat))`
- `Std.Vector` stdlib module -- length-indexed vectors using dependent types

### Added -- Cross-Module Protocol Registry (Phase 2)
- ETS-backed global protocol registry started in `Cure.Application`
- Implementations registered during codegen, discovered at compile time
- `has_impl?` / `lookup_impl` APIs for protocol resolution
- `where Show(T)` constraint validation at call sites
- Cross-module `@derive(Show)` wired into codegen pipeline

### Added -- LSP Production Features (Phase 3)
- `textDocument/definition` with source location tracking
- Type holes: `_` in type annotations inferred and reported as LSP hint diagnostics
- Code actions: add missing match arms, add missing imports, typo correction
- Incremental compilation: AST caching per document URI + version
- Debounced diagnostic publication
- SMT feedback: refinement type info on hover, inline counterexamples

### Added -- Advanced Optimizer (Phase 4)
- Function inlining (small pure functions, recursion-safe)
- Monomorphization at concrete call sites
- Guard simplification (algebraic rules, clause merging, redundancy elimination)
- Pattern-aware SMT encoding for precise exhaustiveness checking
- Deep pipe chain optimizer (Result propagation, Ok wrap/unwrap elimination)
- 5 optimizer passes: inline, constant_fold, dead_code, pipe_inline, guard_simplify

### Added -- FSM Actions & Monitoring (Phase 5)
- Transition actions: `Red --timer--> Green do count = count + 1`
- Guard codegen on transitions: `Red --timer when count > 0--> Green`
- Supervisor-compatible FSM processes with health check API
- Automatic restart tracking (last event time, transition count, error count)

### Added -- Error Reporting (Phase 6)
- CLI uses `format_with_source` for source-annotated errors with caret pointing
- Error catalog with codes E001-E005
- `cure explain E001` command with detailed explanations and examples
- "Did you mean?" suggestions wired into LSP code action quick fixes
- ANSI color output with TTY detection

### Added -- Stdlib Completion (Phase 7)
- `Std.Map` (14 fns) -- put, get, delete, merge, keys, values
- `Std.Set` (11 fns) -- add, remove, member, union, intersection
- `Std.Option` (10 fns) -- separate Option module from Std.Core
- `Std.Functor` (1 fn) -- functor protocol (map over any container)
- Total: 17 stdlib modules, ~200 functions

---

## [0.12.0] -- The Complete Rewrite

Completed the full rewrite from Erlang to Elixir, reimplementing all 12
phases of the original roadmap plus 8 additional phases of advanced features.

### Added -- Import Resolution (Phase A)
- `collect_imports/2` extracts module atoms from `use` declarations
- `resolve_import/3` checks imported modules for matching exports at compile time
- `collect_local_fn_names/1` ensures local functions take priority over imports
- Supports `use Std.List`, `use Std.{List, Core}`

### Added -- Dependent Types (Phase B)
- `Cure.Types.Dependent` -- dependent type representation with value parameters
- Type-level expression substitution
- Verification condition generation for SMT
- Compatibility checking

### Added -- Typeclass Derive (Phase C)
- `Cure.Types.Derive` -- auto-derive Show, Eq, Ord from type structure
- Generates protocol method AST from type name + field list

### Added -- LSP Enhancements (Phase D)
- `Cure.LSP.Symbols` -- symbol extraction from parsed AST
- Hierarchical DocumentSymbol format for `textDocument/documentSymbol`

### Added -- SMT Depth (Phase E)
- `Cure.SMT.Parser` -- Z3 S-expression output parser
- `parse_model/1` extracts variable -> value maps from `(get-model)` output
- General `parse_sexp/1` for nested S-expressions

### Added -- FSM Depth (Phase F)
- `Cure.FSM.TypeSafety` -- FSM transition consistency analysis
- Duplicate transition detection, wildcard shadow detection, self-loop detection

### Added -- Error Reporting Enhancements (Phase G)
- `Cure.Compiler.Errors.suggest/2` -- Levenshtein-based "did you mean?" suggestions
- `format_with_source/3` -- source-annotated errors with caret pointing

### Added -- Remaining Stdlib (Phase H)
- `Std.Eq` (2 fns) -- equality protocol with impls for all primitives
- `Std.Ord` (5 fns) -- ordering protocol with compare, lt, le, gt, ge
- `Std.Result` (11 fns) -- dedicated Result module with flatten

### Stats
- 569 tests, all passing
- 0 credo issues (strict mode)
- 0 compilation warnings
- 44 Elixir source files (~11,500 lines)
- 12 stdlib `.cure` modules (~160 functions)
- 10 example programs
- 4 documentation guides

---

## [0.11.0] -- First Roadmap Complete (Phases 1-12)

### Added -- Standard Library (Phase 1)
- 9 self-hosted stdlib modules (~140 functions) written in Cure itself
- `Std.Core` (36 fns) -- identity, compose, pipe, booleans, comparisons, Result, Option
- `Std.List` (25 fns) -- map, filter, foldl/foldr, flat_map, zip_with, take, drop
- `Std.Math` (18 fns) -- abs, sqrt, pow, log, ceil, floor, pi, max, min, clamp
- `Std.String` (17 fns) -- concat, split, trim, reverse, type conversions
- `Std.Pair` (9 fns) -- first, second, swap, map_first, map_second
- `Std.Io` (8 fns) -- println, print, type-to-string conversions
- `Std.System` (10 fns) -- timestamps, process info, system info
- `Std.Show` (protocol) -- Show with impls for Int, Float, String, Bool, Atom
- `Std.Fsm` (12 fns) -- spawn, send, state, history, lookup
- `mix cure.compile_stdlib` task

### Fixed -- Compiler Bugfixes (Phase 1)
- Lexer: blank/comment-only lines no longer break indentation
- Codegen: variable-as-function calls, lambda closure scoping, chained calls `f(x)(y)`
- Parser: qualified calls via dotted path reconstruction, guard binding power fix

### Added -- Protocol / Typeclass System (Phase 2)
- `Cure.Types.Protocol` -- protocol/impl tracking, type-to-guard mapping
- Codegen: 3-phase module body compilation (collect protos/impls, generate dispatch, compile)
- Type checker: protocol method signature registration, impl body validation
- Dispatch clause ordering by type specificity (Bool before Atom)

### Added -- SMT Solver + Refinement Types (Phase 3)
- `Cure.SMT.Process` -- Z3 GenServer via Erlang port, sentinel-based response parsing
- `Cure.SMT.Translator` -- MetaAST to SMT-LIB2, logic inference (QF_LIA/QF_LRA/QF_NIA)
- `Cure.SMT.Solver` -- check_sat, prove_implication, check_refinement_subtype
- `Cure.Types.Refinement` -- refinement type representation, SMT-backed subtype checking
- `Type.subtype?` extended for refinement-to-base and refinement-to-refinement

### Added -- Guard System Enhancements (Phase 4)
- `Cure.Types.GuardRefinement` -- guard constraint extraction, flow-sensitive refinement
- SMT-backed guard coverage analysis, unreachable clause detection
- Codegen fix: single-body functions with guards compile correctly
- Parser fix: guard expressions parse at BP 6 to stop before `=`

### Added -- Type-Directed Optimizations (Phase 5)
- `Cure.Optimizer` -- pass manager wired into compiler pipeline (`optimize: true`)
- `Cure.Optimizer.ConstantFold` -- arithmetic, boolean, comparison, string, unary folding
- `Cure.Optimizer.DeadCode` -- constant-condition branches, code after return/throw
- `Cure.Optimizer.PipeInline` -- identity elimination in pipe chains

### Added -- Pattern Exhaustiveness Checker (Phase 6)
- `Cure.Types.PatternChecker` -- classify patterns, compute coverage against scrutinee type
- Supports Bool, Result/Option ADTs, List, infinite types (require wildcard)
- Integrated into type checker as `:type_warning` pipeline events

### Added -- FSM Runtime (Phase 7)
- `Cure.FSM.Runtime` -- GenServer with ETS registry, event history, batch operations
- `Cure.FSM.Builtins` -- FFI bridge (fsm_spawn, fsm_send, fsm_state, etc.)
- Started automatically via Application supervisor

### Added -- Language Server Protocol (Phase 8)
- `Cure.LSP.Transport` -- Content-Length framing, JSON-RPC 2.0 over stdio
- `Cure.LSP.Server` -- initialize, textDocument lifecycle, diagnostics, hover, completions
- `cure-lsp` executable for editor integration
- `mix cure.lsp` task

### Added -- Standalone CLI (Phase 9)
- `Cure.CLI` -- escript entry point with 6 subcommands
- `cure compile|run|check|lsp|stdlib|version`
- Options: `--output-dir`, `--type-check`, `--optimize`, `--verbose`

### Added -- MCP Server (Phase 10)
- `Cure.MCP.Server` -- newline-delimited JSON-RPC with 7 tools
- Tools: compile_cure, parse_cure, type_check_cure, analyze_fsm, validate_syntax,
  get_syntax_help, get_stdlib_docs
- `mix cure.mcp` task

### Added -- Extended Examples & Documentation (Phase 11)
- 10 example programs: hello, math, traffic_light, list_basics, result_handling,
  pattern_guards, recursion, protocols, ffi, adt
- 4 doc guides: LANGUAGE_SPEC.md, TYPE_SYSTEM.md, FSM_GUIDE.md, STDLIB.md

### Added -- Profiler & Developer Tools (Phase 12)
- `Cure.Profiler` -- per-stage event counting, total time measurement
- `mix cure.profile` task

---

## [0.10.0] -- Project Bootstrap

Complete rewrite of Cure from Erlang to Elixir using Metastatic's MetaAST
format. Milestones 1-7 of the initial roadmap.

### Added -- Project Bootstrap & Lexer (Milestone 1)
- Elixir project with full tooling (credo, oeditus_credo, ex_doc, dialyxir, excoveralls)
- `Cure.Pipeline.Events` -- Registry-backed PubSub for pipeline stage events
- `Cure.Compiler.Lexer` -- tokenizes all Cure syntax keywords, operators, literals
- Indentation tracking (`:indent`, `:dedent`, `:newline` tokens)
- String interpolation tokenization
- Position tracking (line, column) on every token

### Added -- Parser: Expressions & Bindings (Milestone 2)
- Pratt (precedence-climbing) parser with indentation awareness
- All literal types, variables, binary/unary operators, function calls
- Let bindings, augmented assignment, conditionals, pattern matching
- Blocks, collections (list, tuple, map, range), pipe desugaring
- String interpolation, comprehensions, early return, throw, yield

### Added -- Parser: Definitions, Modules & FSMs (Milestone 3)
- Named function definitions (single-line, multi-line, multi-clause, guards, constraints)
- Modules, records, ADT/sum types, type aliases, refinement types
- Protocols, implementations, imports
- FSM definitions with transitions, wildcards, @terminal, @invariant, @verify
- Metastatic Cure adapter (ToMeta + FromMeta)

### Added -- BEAM Code Generation (Milestone 4)
- `Cure.Compiler.Codegen` -- MetaAST -> Erlang abstract forms
- Module assembly with exports, @extern wrappers, multi-clause functions
- ADT constructors as tagged tuples, records as maps
- `Cure.Compiler.BeamWriter` -- `:compile.forms/2` wrapper + `.beam` file writing
- `Cure.Compiler` -- orchestrator (lex -> parse -> codegen -> beam_write)
- `Mix.Tasks.Cure.Compile` -- `mix cure.compile` task

### Added -- Type System Foundation (Milestone 5)
- `Cure.Types.Type` -- canonical type representations, subtyping, join, AST resolution
- `Cure.Types.Env` -- scoped typing environment with builtins
- `Cure.Types.Checker` -- bidirectional type checker (infer + check modes)
- Two-pass module checking (signatures then bodies), @extern trusted

### Added -- FSM Compilation & Verification (Milestone 6)
- `Cure.FSM.Verifier` -- reachability (BFS), deadlock freedom, terminal state validation
- `Cure.FSM.Compiler` -- FSM MetaAST -> gen_statem Erlang abstract forms
- start_link, send_event, get_state, callback_mode, init, handle_event

### Added -- CLI, Error Reporting, CI, Examples (Milestone 7)
- `Cure.Compiler.Errors` -- structured error formatter for all pipeline stages
- GitHub Actions CI (`.github/workflows/ci.yml`)
- Example programs (hello.cure, math.cure, traffic_light.cure)
- Comprehensive README

### Stats
- 28 source files
- 290 tests, all passing
- 0 credo issues (strict mode)
- Clean dialyzer
