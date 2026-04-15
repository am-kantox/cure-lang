# Cure -- Dependently-typed BEAM Language
Recreation of the Cure language from scratch in Elixir, using Metastatic's MetaAST as the backing AST representation, following the syntax defined in `metastatic/stuff/META_SYNTAX_APPROACH.md`.
Terminology: **Cure** refers to this new implementation. **Cure Legacy** refers to the Erlang PoC in `../Ammotion/cure`.
## Problem Statement
Cure Legacy is a PoC written entirely in Erlang with its own ad-hoc AST records (`cure_ast.hrl`), a hand-rolled lexer/parser, and types bolted on after the fact. The new Cure must:
* Use Metastatic's MetaAST 3-tuple format `{type, meta, children}` as the internal representation
* Follow the Cure syntax from META_SYNTAX_APPROACH.md (indentation-structured, `fn`/`mod`/`rec`/`fsm` keywords, `%[]` tuples, `%{}` maps, etc.)
* Compile to BEAM via Erlang abstract forms (same target as Cure Legacy)
* Build types from day one, not retrofitted
* Keep the core minimal -- standard library in Cure itself later
* Live in `./cure` as an Elixir project
* **Emit events from every pipeline stage** (lexer, parser, type checker, codegen) via a `Cure.Pipeline.Events` system backed by Elixir's `Registry` (PubSub), so that external tools (LSP, profilers, debuggers, IDE plugins) can subscribe to and observe compilation
## Current State
**Cure Legacy (Erlang, `../Ammotion/cure`):**
* ~57 Erlang source files, Erlang records for AST
* Lexer (`cure_lexer.erl`), Parser (`cure_parser.erl`), Codegen (`cure_codegen.erl` + `cure_beam_compiler.erl`)
* Types added late, SMT integration, FSM verifier, LSP, typeclasses -- all tangled
* Old syntax: `module X do ... end`, `def f(x: Int): Int = ...`, `record ... do ... end`
**Metastatic (Elixir, `./metastatic`):**
* Provides MetaAST 3-tuple nodes: `{:literal, meta, value}`, `{:function_def, meta, body}`, etc.
* Three layers: Core (M2.1), Extended (M2.2), Structural (M2.2s)
* Has `Metastatic.AST` traversal, `Metastatic.Document`, `Metastatic.Validator`
* No Cure adapter yet -- we will add one inside Metastatic as `Metastatic.Adapters.Cure`
**Cure Syntax (from META_SYNTAX_APPROACH.md):**
* Indentation-structured (no `do...end`)
* `fn`, `mod`, `rec`, `fsm`, `proto`, `impl`, `type`, `match`, `let`
* Tuples: `%[a, b]`, Maps: `%{k: v}`, Records: `Name{field: val}`
* Exported by default, `local` for private
* `when` for preconditions, `where` for protocol constraints
* FSM: `State --event--> Target`, `@invariant`, `@verify`, `do field = expr`
## Cross-cutting: Pipeline Events
Every stage of the compilation pipeline emits structured events through `Cure.Pipeline.Events`, backed by an Elixir `Registry` in `:duplicate` (PubSub) mode.
**Event structure:** `{stage, event_type, payload, metadata}`
* `stage` -- `:lexer | :parser | :type_checker | :codegen | :fsm_verifier`
* `event_type` -- stage-specific atom (e.g. `:token_produced`, `:node_parsed`, `:type_inferred`, `:form_generated`, `:error`, `:warning`)
* `payload` -- the data (token, AST node, type, form, error struct)
* `metadata` -- `%{file: String.t(), line: pos_integer(), timestamp: integer()}`
**API:**
* `Cure.Pipeline.Events.subscribe(stage)` -- subscribe calling process to events from a stage
* `Cure.Pipeline.Events.subscribe(stage, event_type)` -- subscribe to specific event type
* `Cure.Pipeline.Events.emit(stage, event_type, payload, metadata)` -- emit from inside a pipeline stage
* Events are delivered as standard Erlang messages: `{Cure.Pipeline.Events, stage, event_type, payload, metadata}`
This is used in every milestone; each module documents which events it emits.
## Architecture Overview
```
.cure source
  |  [Lexer]        Cure.Compiler.Lexer           -- emits :lexer events
  v
Token stream
  |  [Parser]       Cure.Compiler.Parser           -- emits :parser events
  v
MetaAST (Metastatic 3-tuples)
  |  [Type System]  Cure.Types.Checker             -- emits :type_checker events
  v
Typed MetaAST (annotated)
  |  [Codegen]      Cure.Compiler.Codegen          -- emits :codegen events
  v
Erlang Abstract Forms
  |  [:compile.forms/2]
  v
BEAM bytecode (.beam files)
```
## Milestone Plan
Each milestone is self-contained: tests pass, docs updated, tagged.
### Milestone 1 -- Project Bootstrap, Pipeline Events & Lexer [DONE]
**Goal:** Elixir project with full tooling, pipeline event infrastructure, lexer that tokenizes the Cure syntax.
1. Create `./cure` Elixir project with `mix new cure`
2. Configure deps: `metastatic` (path), `credo`, `oeditus_credo`, `ex_doc`, `dialyxir`, `excoveralls`
3. Configure `.formatter.exs`, `.credo.exs`, dialyzer PLT paths
4. Create `Cure.Pipeline.Events` module:
    * Start `Registry` in `Cure.Application` (`:duplicate` dispatch for PubSub)
    * `subscribe/1`, `subscribe/2`, `emit/4` functions
    * Docs + tests verifying pub/sub delivery
5. Create `Cure.Compiler.Lexer` module:
    * Tokenize all keywords from Section 3.3 of the syntax spec
    * Handle all operators from Section 3.4
    * Handle all literals from Section 4 (integers, floats, hex, binary, strings, atoms, booleans, nil, regex, char, binary literals)
    * Indentation tracking: emit `:indent`, `:dedent`, `:newline` tokens
    * String interpolation tokenization (`"hello #{expr}"`)
    * Comments (single-line `#`)
    * Position tracking (line, column) on every token
    * Emit `:lexer` pipeline events: `:token_produced`, `:lex_complete`, `:error`
6. Comprehensive tests for lexer: keywords, operators, literals, indentation, interpolation, edge cases
7. ExDoc documentation for all public modules
8. If Metastatic needs changes (e.g. new node types for Cure-specific constructs), apply them in `./metastatic`
### Milestone 2 -- Parser (Expressions & Bindings) [DONE]
**Goal:** Parse core Cure expressions into Metastatic MetaAST 3-tuples via a Pratt (precedence-climbing) parser with indentation awareness.
* Pratt parser with prefix/infix/postfix binding powers
* All literal types, variables, binary/unary operators, function calls
* Let bindings, augmented assignment, conditionals, pattern matching
* Blocks, collections (list, tuple, map, range), pipe desugaring
* String interpolation, comprehensions, early return, throw, yield
* Error recovery and pipeline event emission
### Milestone 3 -- Parser (Definitions, Modules & FSMs) [DONE]
**Goal:** Parse all top-level and structural constructs into MetaAST, completing the full Cure parser. Build the Metastatic Cure adapter.
* Named function definitions (single-line, multi-line, multi-clause, guards, constraints)
* Modules, records, ADT/sum types, type aliases, refinement types
* Protocols, implementations, imports
* FSM definitions with transitions, wildcards, @terminal, @invariant, @verify
* Decorator attachment (@extern, @doc, etc.)
* Enhanced type expression parser (function types, refinements)
* Metastatic Cure adapter (ToMeta + FromMeta)
### Milestone 4 -- BEAM Code Generation, Compiler Orchestrator & Standard Library [DONE]
**Goal:** Compile Cure MetaAST directly to BEAM bytecode via Erlang abstract forms, wire up a compiler orchestrator, write a minimal standard library in Cure itself.
* `Cure.Compiler.Codegen`: MetaAST -> Erlang abstract forms for all expression types
* Module assembly with exports, @extern wrappers, multi-clause functions
* ADT constructors as tagged tuples, records as maps
* `Cure.Compiler.BeamWriter`: `:compile.forms/2` wrapper + `.beam` file writing
* `Cure.Compiler`: orchestrator (lex -> parse -> codegen -> beam_write)
* `Mix.Tasks.Cure.Compile`: `mix cure.compile` task
* Pipeline event emission at codegen stage
### Milestone 5 -- Type System Foundation [DONE]
**Goal:** Bidirectional type checker that validates MetaAST, annotates it with inferred types, and rejects ill-typed programs.
* `Cure.Types.Type`: canonical type representations, subtyping, join, AST resolution
* `Cure.Types.Env`: scoped typing environment with builtins
* `Cure.Types.Checker`: bidirectional type checker (infer + check modes)
  * Literals, variables, operators, function defs/calls, let bindings
  * Conditionals, pattern matching, blocks, collections, lambdas
  * Two-pass module checking (signatures then bodies)
  * @extern trusted, multi-clause agreement checking
* Optional integration into compiler orchestrator (`check_types: true`)
* `:type_checker` pipeline events
### Milestone 6 -- FSM Compilation & Verification [DONE]
**Goal:** Compile first-class FSM definitions to `gen_statem` BEAM modules and run structural verification.
* `Cure.FSM.Verifier`: reachability (BFS), deadlock freedom, terminal state validation
* `Cure.FSM.Compiler`: FSM MetaAST -> gen_statem Erlang abstract forms
  * start_link, send_event, get_state, callback_mode, init, handle_event
  * Transition clauses with wildcard expansion
* Integrated into `Cure.Compiler.Codegen` via container dispatch
* `:fsm_verifier` pipeline events
### Milestone 7 -- CLI polish, Error Reporting, CI, Examples & Documentation [DONE]
**Goal:** Production-ready CLI experience, structured error messages with source locations, GitHub Actions CI, example programs, comprehensive documentation.
* `Cure.Compiler.Errors`: structured error formatter for all pipeline stages
* Enhanced `Mix.Tasks.Cure.Compile` with formatted error output
* GitHub Actions CI (`.github/workflows/ci.yml`)
* Example programs (`examples/hello.cure`, `examples/math.cure`, `examples/traffic_light.cure`)
* Comprehensive README with architecture, usage, module listing, examples
## Final Stats (v0.10.0)
* **28 source files**, 516 modules/functions
* **290 tests**, all passing
* **Zero credo issues** (strict mode)
* **Clean dialyzer** (0 actionable warnings)
* **Milestones 1-7** complete
