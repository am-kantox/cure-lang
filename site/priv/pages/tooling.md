%{
  title: "Tooling",
  description: "CLI, Language Server, MCP server, optimizer, profiler, and pipeline events.",
  order: 7
}
---

Cure ships with a CLI, an LSP server, an MCP server for AI integration, a
five-pass optimizer, a structured error catalog, a compilation profiler, and
a PubSub event system that lets external tools observe every stage of the
compilation pipeline.

## CLI

The `cure` escript is the primary interface. Build it with `mix escript.build`.

```bash
cure <command> [options] [arguments]
```

### Subcommands

**`cure compile <file|dir>`** -- Compile `.cure` files to BEAM bytecode.

```bash
cure compile hello.cure
cure compile src/               # compiles all .cure files recursively
cure compile hello.cure --output-dir _build/cure/ebin --optimize --verbose
```

Options:

- `--output-dir DIR` (`-o`) -- output directory (default: `_build/cure/ebin`)
- `--no-type-check` -- skip type checking
- `--optimize` -- enable optimization passes
- `--verbose` (`-v`) -- show detailed compilation output

**`cure run <file>`** -- Compile and execute a `.cure` file. Calls `main/0` if
it exists. Type checking is off by default for `run` (use `--type-check` to
enable).

```bash
cure run examples/hello.cure
cure run examples/recursion.cure --optimize
```

**`cure check <file>`** -- Type-check without compiling. Runs lexer, parser,
and type checker, then reports errors or prints `<file>: OK`.

```bash
cure check lib/std/core.cure
```

**`cure lsp`** -- Start the Language Server Protocol server over stdio.

```bash
cure lsp
```

**`cure stdlib`** -- Compile all `.cure` files in `lib/std/` to BEAM bytecode.

```bash
cure stdlib
cure stdlib --output-dir _build/cure/ebin
```

**`cure version`** -- Print the Cure version.

**`cure init <name>`** -- Create a new Cure project with `Cure.toml` and
`lib/main.cure`.

```bash
cure init my_project
```

**`cure deps`** -- Resolve dependencies from `Cure.toml`.

**`cure test`** -- Run test files from `test/`. Compiles each `.cure` file,
then calls all exported functions whose names start with `test`. Reports
pass/fail counts.

```bash
cure test
```

**`cure doc [path|dir]`** -- Generate HTML documentation from `.cure` files.

```bash
cure doc                         # documents all .cure files in lib/
cure doc lib/std/ --output-dir _build/cure/doc --title "Cure Stdlib"
```

Options:

- `--output-dir DIR` -- output directory (default: `_build/cure/doc`)
- `--title TITLE` -- project title for the index page

**`cure fmt [path|dir]`** -- Format `.cure` source files in place.

As of v0.21.0, the default formatter is the
**Wadler/`Inspect.Algebra`-style pretty printer** built on
`Cure.Compiler.Algebra` and `Cure.Compiler.AlgebraFormatter`. It
uses a best-fit line-wrapping algorithm, separates top-level
definitions with blank lines, and round-trips plain `#` comments
(lexed under `preserve_comments: true`) as real `# ...` lines in
source order. Every rewrite is round-trip-validated against the
original AST modulo comment placement; if verification fails, the
file is left untouched, so the formatter is non-destructive by
construction.

```bash
cure fmt                         # algebra formatter (default)
cure fmt lib/std/core.cure       # format a specific file
cure fmt --check                 # CI mode: exits 1 if any file would change
cure fmt --safe                  # legacy byte-level safe formatter
cure fmt --aggressive            # legacy AST rewrite; strips comments
```

Options:

- `--check` -- report files that would be reformatted and exit
  non-zero; leaves files on disk untouched. v0.21.0 routes
  `--check` through the algebra formatter so CI agrees with
  interactive use.
- `--safe` -- v0.20.0 byte-level formatter. Normalises line endings,
  strips trailing whitespace, expands leading tabs into two spaces,
  collapses runs of blank lines to a single blank line,
  canonicalises operator spacing, and ensures a single trailing
  newline. Kept as an escape hatch for sources that trip the
  algebra formatter's round-trip check.
- `--algebra` -- explicit opt-in to the algebra formatter;
  synonymous with the default since v0.21.0.
- `--aggressive` / `--ast` -- legacy AST pretty printer
  (`Cure.Compiler.Printer`). Strips plain `#` comments and any
  non-canonical whitespace. Prints a warning before touching
  files.

**`cure repl`** -- Start a minimal interactive Cure session. Each expression
is compiled via `compile_and_load` and its result printed.

```bash
cure repl
```

**`cure explain <code>`** -- Look up a structured error explanation.

```bash
cure explain E001
cure explain E010
```

**`cure help`** -- Show usage information.

---

## LSP Server

The LSP server implements the Language Server Protocol over stdio. It provides
real-time feedback in any editor that supports LSP.

### Capabilities

- **Text document synchronization** -- full sync mode. The server re-analyzes
  the entire document on every change.
- **Diagnostics** -- compile errors and type errors reported on every keystroke.
  Each diagnostic includes file, line, and a description.
- **Hover** -- shows function signatures, type information, and inferred
  effects when hovering over identifiers.
- **Completion** -- triggered by `.` and `:`, provides keyword completions.
- **Go-to-definition** (v0.13) -- jump to the definition of functions and
  modules.
- **Document symbols** (v0.13) -- hierarchical outline of modules, functions,
  protocols, and FSM definitions.
- **Code actions** (v0.13) -- quick-fix suggestions:
  - Add wildcard pattern for non-exhaustive matches.
  - "Did you mean?" suggestions for unbound variables (Levenshtein distance).

### AST caching

The server caches parsed ASTs per document version. If a `didChange`
notification arrives with the same version number, the server skips
re-parsing and re-diagnosing. This reduces redundant work during rapid edits.

### Neovim configuration

```lua
vim.api.nvim_create_autocmd("FileType", {
  pattern = "cure",
  callback = function()
    vim.lsp.start({
      name = "cure-lsp",
      cmd = { "cure", "lsp" },
      root_dir = vim.fs.dirname(
        vim.fs.find({ "Cure.toml", "mix.exs" }, { upward = true })[1]
      ),
    })
  end,
})
```

### VS Code (generic LSP client)

Any VS Code extension that supports custom LSP servers can be pointed at
`cure lsp`. Set the command to the absolute path of the `cure` escript.

---

## MCP Server

The Model Context Protocol server provides AI tool integration via JSON-RPC
2.0 over newline-delimited stdio. Start it with `mix cure.mcp`.

### Tools

7 tools are exposed:

**`compile_cure`** -- Compile Cure source code. Returns the module name and
exports on success, or error details.

```json
{"name": "compile_cure", "arguments": {"source": "mod Hello\n  fn main() -> Int = 42"}}
```

**`parse_cure`** -- Parse source and return an AST summary.

**`type_check_cure`** -- Type-check source. Returns errors and warnings.

**`analyze_fsm`** -- Analyze an FSM definition. Returns states, transitions,
and verification results (reachability, deadlock freedom).

**`validate_syntax`** -- Quick syntax validation (lex + parse only, no type
checking).

**`get_syntax_help`** -- Get help on a Cure syntax topic. Topics: `functions`,
`types`, `fsm`, `protocols`, `pattern_matching`, `modules`, `records`.

**`get_stdlib_docs`** -- Get documentation for a stdlib module by name
(e.g., `Std.List`, `Std.Core`).

### Protocol

The server speaks MCP protocol version `2024-11-05`. On `initialize`, it
returns its capabilities. Tools are listed via `tools/list` and invoked via
`tools/call`.

---

## Optimizer

The optimizer runs 5 transformation passes on the MetaAST between type
checking and code generation. Enable it with `--optimize` on the CLI or
`optimize: true` in compiler options.

```elixir
{:ok, optimized_ast, stats} = Cure.Optimizer.optimize(ast)
```

### Pass 1: Inline

Small, pure, non-recursive functions are inlined at their call sites. The
function body replaces the call expression with arguments substituted.

Before:
```cure
fn double(x: Int) -> Int = x * 2
fn main() -> Int = double(21)
```

After optimization: `main` compiles to `21 * 2`.

### Pass 2: Constant fold

Evaluates constant expressions at compile time. Covers arithmetic (`+`, `-`,
`*`, `/`, `%`), boolean operations (`and`, `or`, `not`), string concatenation
(`<>`), and comparisons (`==`, `!=`, `<`, `>`, `<=`, `>=`).

Before:
```cure
fn answer() -> Int = 6 * 7
fn greeting() -> String = "hello" <> " " <> "world"
```

After optimization: `answer` returns the literal `42`, `greeting` returns
`"hello world"`.

### Pass 3: Dead code elimination

Removes unreachable code:

- `if true then A else B` -> `A`
- `if false then A else B` -> `B`
- Code after `return` or `throw` is dropped.

### Pass 4: Pipe inline

Simplifies pipe chains by converting `a |> f |> g` into direct calls `g(f(a))`.
Also eliminates identity functions in pipe chains: `x |> identity |> f` becomes
`f(x)`.

### Pass 5: Guard simplify

Applies algebraic boolean simplification rules to guard expressions:

- `P and P` -> `P`
- `P or P` -> `P`
- `true and P` -> `P`
- `false and P` -> `false`
- `true or P` -> `true`
- `false or P` -> `P`
- `not not P` -> `P`
- `not true` -> `false`
- `not false` -> `true`

### Statistics

The optimizer returns a stats map counting transformations per pass:

```elixir
%{inline: 3, constant_fold: 7, dead_code: 2, pipe_inline: 1, guard_simplify: 0}
```

Individual passes can be run in isolation:

```elixir
{:ok, ast, count} = Cure.Optimizer.run_pass(ast, :constant_fold)
```

---

## Error Catalog

Cure uses structured error codes. Each code has a detailed explanation
accessible via `cure explain <code>`.

**E001: Type Mismatch** -- A function's body type does not match its declared
return type, or an argument type does not match the parameter type.

```cure
fn add(a: Int, b: Int) -> String = a + b
# error E001: declared return type String but body has type Int
```

**E002: Unbound Variable** -- A variable is referenced that has not been defined.

```cure
fn foo() -> Int = x + 1
# error E002: undefined variable 'x'
```

**E003: Arity Mismatch** -- A function is called with the wrong number of
arguments.

```cure
fn add(a: Int, b: Int) -> Int = a + b
fn main() -> Int = add(1)
# error E003: expects 2 arguments, got 1
```

**E004: Non-Exhaustive Match** -- A match expression does not cover all
possible patterns.

```cure
match x
  true -> "yes"
# warning E004: missing pattern for 'false'
```

**E005: Constraint Violation** -- A function with a guard constraint is
called with arguments that may violate the constraint. The compiler uses Z3
to check this.

```cure
fn safe_div(a: Int, b: Int) -> Int when b != 0 = a / b
fn main() -> Int = safe_div(10, 0)
# warning E005: b != 0 may be violated (counterexample: b = 0)
```

**E006: Effect Violation** -- A function performs an effect not declared in
its `!` annotation.

**E007: Unused Variable** -- A `let` binding or parameter is defined but
never referenced. Prefix with `_` to suppress.

**E008: Undocumented Public Function** -- A public function has no `##` doc
comment. Emitted only in `cure doc --strict` mode.

**E009: Unreachable Clause** -- A pattern matching clause is shadowed by a
prior clause.

**E010: Missing Effect Annotation** -- A public function performs side effects
but has no `!` annotation. Emitted only in `--strict-effects` mode.

### Dependent-type and pattern codes (v0.17.0+)

**E011: Missing Implicit Argument** -- first-order unification could not
solve every implicit parameter at a call site. The unification trace names
the constraint that failed.

**E012: Sigma Destructuring Failure** -- pattern attempted to destructure a
sigma value against shapes that disagree with its declared components.

**E013: Totality Failure** -- a `#[total]`-annotated function is not provably
total.

**E014: Unfilled Hole** -- a `?name` or `??` placeholder remained unfilled.
Informational unless `cure check --strict` is active.

**E015: Refinement Counterexample** -- a value flowing into a refinement-typed
parameter might violate the predicate; the Z3 model gives a witness.

**E016: Dependent Type Mismatch** -- a dependent return type does not match
the expected type at the use site after substitution and reduction.

**E017: Equality Proof Mismatch** -- `refl(x)` was used to inhabit
`Eq(T, a, b)` where `a` and `b` are not definitionally equal to `x`.

**E018: Path-sensitive Refinement Conflict** -- a path-sensitive refinement
extracted from a guard contradicts a previously declared refinement.

**E019: Implicit Argument Solved Inconsistently** -- the same implicit was
solved to two different types from different parts of the call site.

**E020: Doctest Mismatch** -- a `cure>` doctest produced a different value
from its `=>` expected line.

### Pattern engine codes (v0.18.0)

**E021: Unknown Record Field in Pattern** -- a record pattern references a
field that is not declared in the record's schema.

**E022: Record Pattern Field Type Mismatch** -- a sub-pattern inside a record
pattern is incompatible with the declared type of that field.

**E023: Non-Literal Map Pattern Key** -- map keys in pattern position must
be literal values (atoms, integers, strings, ...).

**E024: Unbound Pin Variable** -- the pin operator `^x` was used on a name
that is not in scope at the pattern's position.

**E025: Non-Exhaustive Nested Match** -- a `match` with nested patterns does
not cover every inhabitant of the scrutinee type; the compiler prints a
concrete missing witness.

### v0.19.0 codes

**E026: Proof Shape Mismatch** -- a binding inside a `proof` container does
not elaborate to an `Eq(...)` or refinement proof.

**E027: `assert_type` Assertion Failed** -- the expression in
`assert_type expr : T` does not match `T`.

**E028: Record Default Type Mismatch** -- a record field's default value
does not match the declared field type.

**E029: Mutual Recursion Not Structural** -- a `#[total]` function takes
part in a cycle in which no argument shrinks on every path.

**E030: Package Version Conflict** -- the dependency resolver could not find
a set of versions satisfying every active constraint.

### v0.21.0 codes

**E031: Binary Pattern Not Exhaustive** -- a sequence of binary patterns
(in a `match`, function head, `let`, or comprehension generator) does not
cover every byte-length inhabitant of the scrutinee's Bitstring type. The
compiler prints a concrete missing witness such as `"<<>>"` or
`"<<_, _rest::binary>>"`.

**E032: Function Type Payload Invalid** -- an ADT constructor payload
carries a value whose type cannot be resolved. Function-type payloads
(e.g. `On(Int -> Int)` and `On((Int, Int) -> Int)`) are allowed and compile
to first-class functions at runtime.

**E033: Multi-line Type Layout Invalid** -- a `type` ADT declaration
spans multiple lines but the layout cannot be absorbed by the type-def
recogniser. Usually means the continuation lines are not indented
beyond the `type` keyword.

**E034: Let Pattern Not Exhaustive** -- a `let` binding destructures its
RHS with a pattern that does not cover every inhabitant of the RHS type.
The binding still compiles -- Erlang's `=` raises at runtime on a failed
match -- but the compiler surfaces the gap as a warning.

### Error formatting

Errors include source location with caret display:

```
error: type mismatch in function 'bad'
 --> hello.cure:3
  | declared return type Int but body has type String
```

The compiler also suggests corrections for typos using Levenshtein distance
("Did you mean `length`?").

---

## Pipeline Events

Every stage of the compilation pipeline emits structured events through a
Registry-backed PubSub system. External tools (LSPs, profilers, debuggers,
IDE plugins) can subscribe and observe compilation in real time.

### Event structure

Events are 4-tuples: `{stage, event_type, payload, metadata}`

- **stage** -- `:lexer`, `:parser`, `:type_checker`, `:codegen`, `:fsm_verifier`
- **event_type** -- stage-specific atom (e.g., `:token_produced`, `:node_parsed`,
  `:form_generated`, `:error`)
- **payload** -- the data (token, AST node, error, etc.)
- **metadata** -- `%{file: String.t(), line: pos_integer(), timestamp: integer()}`

### Subscribing

```elixir
# Subscribe to all events from the lexer
Cure.Pipeline.Events.subscribe(:lexer)

# Subscribe only to errors from the parser
Cure.Pipeline.Events.subscribe(:parser, :error)
```

### Receiving events

Events are delivered as standard Erlang messages:

```elixir
receive do
  {Cure.Pipeline.Events, :lexer, :token_produced, token, meta} ->
    IO.inspect(token)
end
```

### Emitting (internal)

Pipeline stages use `emit/4`:

```elixir
Cure.Pipeline.Events.emit(:codegen, :form_generated, form, Events.meta(file, line))
```

Emission can be disabled with `emit_events: false` in compiler options (which
the CLI uses by default for non-profiling runs).

---

## Profiler

The profiler measures per-stage event counts and total compilation time by
subscribing to pipeline events.

### Usage

```elixir
{:ok, report} = Cure.Profiler.profile_file("hello.cure")
IO.puts(Cure.Profiler.format_report(report))

{:ok, report} = Cure.Profiler.profile_string(source, check_types: true, optimize: true)
```

### Report structure

```elixir
%{
  file: "hello.cure",
  source_bytes: 142,
  total_us: 1523,
  stages: %{
    lexer: %{count: 24},
    parser: %{count: 12},
    codegen: %{count: 8}
  },
  event_count: 44,
  result: "success"
}
```

### Formatted output

```
Cure Compilation Profile
========================
File:         hello.cure
Source:       142 bytes
Total time:   1.52 ms
Events:       44
Result:       success

Pipeline Stages:
  lexer                24     events
  parser               12     events
  codegen              8      events
```

The profiler subscribes to all 5 pipeline stages (`:lexer`, `:parser`,
`:type_checker`, `:codegen`, `:fsm_verifier`), drains events after compilation
completes, and groups them by stage.
