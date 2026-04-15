# Cure -- Implementation Plan for v0.12.0

Recreation of the Cure language from the Erlang PoC (`../Ammotion/cure`, 57 source files) as a clean Elixir implementation using Metastatic's MetaAST.

Terminology: **Cure** refers to this implementation. **Cure Legacy** refers to the Erlang PoC.

## Starting Point (v0.10.0, milestones 1-7)

The new Cure already had:
- Full lexer with indentation tracking, string interpolation, position tracking
- Pratt parser producing MetaAST 3-tuples (all expressions, definitions, modules, records, ADTs, FSMs, protocols, imports)
- Bidirectional type checker (literals, variables, operators, functions, let bindings, conditionals, pattern matching, blocks, collections, lambdas, two-pass modules)
- BEAM codegen via Erlang abstract forms (expressions, patterns, module assembly, `@extern` FFI, multi-clause, ADT constructors, records as maps)
- FSM compiler (gen_statem) + structural verifier (reachability, deadlocks, terminals)
- Pipeline event system (Registry PubSub)
- `mix cure.compile` CLI task, structured error formatter, CI, 3 examples, 290 tests

---

## First Roadmap: Phases 1-12 (v0.10 -> v0.11)

### Phase 1 -- Standard Library [DONE]
9 self-hosted stdlib modules (~140 functions) written in Cure itself:
- `Std.Core` (36 fns) -- identity, compose, pipe, booleans, comparisons, Result, Option
- `Std.List` (25 fns) -- map, filter, foldl/foldr, flat_map, zip_with, take, drop, sum, product
- `Std.Math` (18 fns) -- abs, sqrt, pow, log, ceil, floor, pi, max, min, clamp, sign
- `Std.String` (17 fns) -- concat, split, trim, reverse, type conversions
- `Std.Pair` (9 fns) -- first, second, swap, map_first, map_second
- `Std.Io` (8 fns) -- println, print, type-to-string conversions
- `Std.System` (10 fns) -- timestamps, process info, system info
- `Std.Show` (protocol) -- Show with impls for Int, Float, String, Bool, Atom
- `Std.Fsm` (12 fns) -- spawn, send, state, history, lookup
- `mix cure.compile_stdlib` task

Compiler bugfixes discovered during stdlib work:
- Lexer: blank/comment-only lines no longer break indentation
- Codegen: variable-as-function calls, lambda closure scoping, chained calls f(x)(y)
- Parser: qualified calls via dotted path reconstruction, guard BP fix

### Phase 2 -- Protocol / Typeclass System [DONE]
- `Cure.Types.Protocol` -- protocol/impl tracking, type-to-guard mapping, dispatch clause generation
- Codegen: 3-phase module body compilation (collect protos/impls, generate dispatch, compile functions)
- Type checker: protocol method signature registration, impl body validation
- Dispatch clause ordering by type specificity (Bool before Atom)

### Phase 3 -- SMT Solver + Refinement Types [DONE]
- `Cure.SMT.Process` -- Z3 GenServer via Erlang port, sentinel-based response parsing
- `Cure.SMT.Translator` -- MetaAST to SMT-LIB2, logic inference (QF_LIA/QF_LRA/QF_NIA)
- `Cure.SMT.Solver` -- check_sat, prove_implication, check_refinement_subtype, is_satisfiable?
- `Cure.Types.Refinement` -- refinement type representation, SMT-backed subtype checking
- `Type.resolve` produces refinement types from parser AST
- `Type.subtype?` extended for refinement-to-base and refinement-to-refinement

### Phase 4 -- Guard System Enhancements [DONE]
- `Cure.Types.GuardRefinement` -- guard constraint extraction, flow-sensitive type refinement, SMT-backed guard coverage analysis, unreachable clause detection
- Type checker integration: per-clause guard refinement, coverage warnings
- Codegen fix: single-body functions with guards now compile correctly
- Parser fix: guard expressions parse at BP 6 to stop before `=`

### Phase 5 -- Type-Directed Optimizations [DONE]
- `Cure.Optimizer` -- pass manager wired into compiler pipeline (opt-in via `optimize: true`)
- `Cure.Optimizer.ConstantFold` -- arithmetic, boolean, comparison, string, unary folding
- `Cure.Optimizer.DeadCode` -- constant-condition branches, code after return/throw
- `Cure.Optimizer.PipeInline` -- identity elimination in pipe chains

### Phase 6 -- Pattern Exhaustiveness Checker [DONE]
- `Cure.Types.PatternChecker` -- classify patterns, compute coverage against scrutinee type
- Supports Bool, Result/Option ADTs, List, infinite types (require wildcard)
- Integrated into type checker as `:type_warning` pipeline events

### Phase 7 -- FSM Runtime [DONE]
- `Cure.FSM.Runtime` -- GenServer with ETS registry, event history, batch operations, process monitoring
- `Cure.FSM.Builtins` -- FFI bridge (fsm_spawn, fsm_send, fsm_state, etc.)
- Started automatically via Application supervisor

### Phase 8 -- Language Server Protocol [DONE]
- `Cure.LSP.Transport` -- Content-Length framing, JSON-RPC 2.0 over stdio
- `Cure.LSP.Server` -- initialize, textDocument lifecycle, diagnostics, hover, completions
- Content-Length-aware stdin reader for escript compatibility
- `cure-lsp` executable for editor integration
- `mix cure.lsp` task

### Phase 9 -- Standalone CLI [DONE]
- `Cure.CLI` -- escript entry point with 6 subcommands
- `cure compile|run|check|lsp|stdlib|version`
- Options: `--output-dir`, `--type-check`, `--optimize`, `--verbose`
- Configured in `mix.exs` as escript build

### Phase 10 -- MCP Server [DONE]
- `Cure.MCP.Server` -- newline-delimited JSON-RPC with 7 tools
- Tools: compile_cure, parse_cure, type_check_cure, analyze_fsm, validate_syntax, get_syntax_help, get_stdlib_docs
- `mix cure.mcp` task

### Phase 11 -- Extended Examples & Documentation [DONE]
- 10 example programs: hello, math, traffic_light, list_basics, result_handling, pattern_guards, recursion, protocols, ffi, adt
- 4 doc guides: LANGUAGE_SPEC.md, TYPE_SYSTEM.md, FSM_GUIDE.md, STDLIB.md

### Phase 12 -- Profiler & Developer Tools [DONE]
- `Cure.Profiler` -- per-stage event counting, total time measurement
- `mix cure.profile` task

---

## Second Roadmap: Phases A-H (v0.11 -> v0.12)

Gap analysis identified ~8750 lines of unported legacy Erlang across 19 modules.

### Phase A -- Import Resolution [DONE]
- Codegen: `collect_imports/2` extracts module atoms from `use` declarations
- `resolve_import/3` checks imported modules for matching exports at compile time
- `collect_local_fn_names/1` ensures local functions take priority over imports
- Supports `use Std.List`, `use Std.{List, Core}`

### Phase B -- Dependent Types [DONE]
- `Cure.Types.Dependent` -- dependent type representation with value parameters
- Type-level expression substitution
- Verification condition generation for SMT
- Compatibility checking

### Phase C -- Typeclass Derive [DONE]
- `Cure.Types.Derive` -- auto-derive Show, Eq, Ord from type structure
- Generates protocol method AST from type name + field list

### Phase D -- LSP Enhancements [DONE]
- `Cure.LSP.Symbols` -- symbol extraction from parsed AST
- Hierarchical DocumentSymbol format for textDocument/documentSymbol

### Phase E -- SMT Depth [DONE]
- `Cure.SMT.Parser` -- Z3 S-expression output parser
- `parse_model/1` extracts variable -> value maps from `(get-model)` output
- General `parse_sexp/1` for nested S-expressions

### Phase F -- FSM Depth [DONE]
- `Cure.FSM.TypeSafety` -- FSM transition consistency analysis
- Duplicate transition detection, wildcard shadow detection, self-loop detection

### Phase G -- Error Reporting Enhancements [DONE]
- `Cure.Compiler.Errors.suggest/2` -- Levenshtein-based "did you mean?" suggestions
- `format_with_source/3` -- source-annotated errors with caret pointing

### Phase H -- Remaining Stdlib [DONE]
- `Std.Eq` (2 fns) -- equality protocol with impls for all primitives
- `Std.Ord` (5 fns) -- ordering protocol with compare, lt, le, gt, ge
- `Std.Result` (11 fns) -- dedicated Result module with flatten

---

## Final Stats (v0.12.0)
- **569 tests**, all passing
- **0 credo issues** (strict mode)
- **0 compilation warnings**
- **44 Elixir source files** (~11,500 lines)
- **12 stdlib `.cure` modules** (~160 functions)
- **10 example programs**
- **4 documentation guides**
- **Phases 1-12 + A-H**: all complete
