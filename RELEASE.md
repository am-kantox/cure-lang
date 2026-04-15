# Cure v0.15.0 -- Developer Experience

Cure is a dependently-typed programming language for the BEAM virtual machine
with first-class finite state machines and SMT-backed verification.

v0.15.0 focuses on developer experience: a public `Cure.quote` / `Cure.quoted_to_string`
API (modeled after Elixir's `quote` and `Macro.to_string`), an effect system that
tracks side effects through the type system, HTML documentation generation,
a code formatter, and an interactive REPL.

## Highlights

### Public API
- `Cure.quote/2` -- parse Cure source into MetaAST 3-tuples
- `Cure.quoted_to_string/2` -- convert MetaAST back to Cure source (round-trip capable)
- Clean entry point for tooling, macros, and metaprogramming

### Effect System
- `Cure.Types.Effects` -- infer side effects from function bodies (IO, state, exception, spawn, extern)
- Effect checking: declared effects validated against inferred effects
- `@extern` classification by target module (`:io` -> IO, `:ets` -> state, etc.)
- Pipeline event emission for effect inference results
- Pure functions identified for aggressive optimization

### Source Printer
- `Cure.Compiler.Printer` -- full AST-to-source printer covering all Cure constructs
- Handles literals, operators, bindings, conditionals, pattern matching, collections,
  comprehensions, lambdas, function definitions, containers (mod/rec/enum/proto/impl/fsm),
  type annotations, decorators, imports, exception handling
- Round-trip verified: `quote -> print -> re-quote` produces equivalent AST

### Documentation Generator
- `Cure.Doc.Extractor` -- extract structured docs from module ASTs
- `Cure.Doc.HTMLGenerator` -- static HTML docs with dark/light theme (system preference)
- Per-module pages with function signatures, types, protocols, effects, badges
- `cure doc [path]` CLI command

### Code Formatter
- `cure fmt [path]` -- format `.cure` source files via parse-then-print
- Consistent indentation and style across projects

### Interactive REPL
- `cure repl` -- evaluate Cure expressions interactively
- Wraps input in temporary modules, compiles and executes on the fly
- `:quit` / `:q` / `:exit` to exit

### Compiler Refactoring
- `Cure.Compiler.Token` -- extracted Token struct with type, value, line, col
- `Cure.Compiler.Parser.Precedence` -- extracted Pratt parser binding power table

### Standard Library
18 self-hosted modules:
Std.Core, Std.List, Std.Math, Std.String, Std.Pair, Std.Io,
Std.System, Std.Show, Std.Fsm, Std.Eq, Std.Ord, Std.Result,
Std.Map, Std.Set, Std.Option, Std.Functor, Std.Vector, Std.Test

### Tooling
- Standalone CLI: `cure compile|run|check|lsp|stdlib|init|deps|test|doc|fmt|repl|explain|version|help`
- LSP server: diagnostics, hover, completions, document symbols, definition, code actions
- MCP server: 7 AI tools for compile/parse/check/analyze/help
- Compilation profiler with per-stage event tracking
- `cure-lsp` executable for editor integration

## Changes since v0.14.0

### New modules
- `Cure.quote/2`, `Cure.quoted_to_string/2` -- public parsing/printing API
- `Cure.Compiler.Printer` -- MetaAST to Cure source code
- `Cure.Compiler.Token` -- token struct (extracted from Lexer)
- `Cure.Compiler.Parser.Precedence` -- binding power table (extracted from Parser)
- `Cure.Doc.Extractor` -- documentation extraction from AST
- `Cure.Doc.HTMLGenerator` -- static HTML doc generation
- `Cure.Types.Effects` -- effect inference and checking

### New CLI commands
- `cure doc [path|dir]` -- generate HTML documentation
- `cure fmt [path|dir]` -- format Cure source files
- `cure repl` -- interactive Cure session

### New stdlib
- `Std.Test` (5 fns) -- assert, assert_eq, assert_ne, assert_gt, assert_lt

### New examples
- `dependent_types.cure` -- refinement types and guarded functions
