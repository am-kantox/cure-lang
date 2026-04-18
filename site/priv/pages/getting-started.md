%{
  title: "Getting Started",
  description: "Install and run your first Cure program.",
  order: 1
}
---
## Prerequisites

Cure requires:

- **Elixir** ~> 1.18 and **Erlang/OTP** (the version compatible with your Elixir)
- **Git** for cloning the repository
- **Z3 SMT solver** (optional) -- needed only for refinement type verification. Install via your package manager (`apt install z3`, `brew install z3`, etc.). If Z3 is not present, the compiler skips SMT-backed checks and emits a warning.

## Installation

Clone the repository and fetch dependencies:

```bash
git clone https://github.com/am-kantox/cure-lang.git
cd cure
mix deps.get
mix compile
```

## Building the escript

Cure {{cure_vversion}} ships with a standalone CLI. Build it with the dedicated Mix
task:

```bash
mix cure.escript
```

This compiles the project and produces a `cure` binary in the project root.
Move it somewhere on your `$PATH` to use it globally:

```bash
cp cure ~/.local/bin/
```

Verify the installation:

```bash
cure version
# Cure {{cure_version}}
```

## Hello World

Create a file `examples/hello.cure`:

```cure
mod Hello
  fn greet(name: String) -> String = "Hello, " <> name <> "!"
  fn main() -> Int = 42
```

Every Cure module starts with `mod ModuleName`. Functions are declared with `fn`, typed parameters, a return type annotation, and a body after `=`. The last expression in a block is its return value.

## Compiling

```bash
cure compile examples/hello.cure
```

This runs the full pipeline -- lexer, parser, bidirectional type checker, BEAM code generation -- and writes a `.beam` file to `_build/cure/ebin/`. You can specify a different output directory:

```bash
cure compile examples/hello.cure --output-dir ./out
```

Compile an entire directory at once:

```bash
cure compile examples/ --output-dir _build/cure/ebin
```

## Running

```bash
cure run examples/hello.cure
```

This compiles the file, loads the module into the VM, and calls `main/0` if it exists. The return value is printed to stdout (unless it is `:ok` or `nil`).

## Type checking

To type-check without generating BEAM output:

```bash
cure check examples/hello.cure
```

This runs the lexer, parser, and bidirectional type checker, then reports any type errors or warnings. No `.beam` file is produced.

## Compiling the standard library

The standard library is self-hosted -- written in Cure under `lib/std/`. Compile it with:

```bash
cure stdlib
```

Or via the Mix task:

```bash
mix cure.compile_stdlib
```

This compiles all `.cure` files in `lib/std/` and writes the resulting `.beam` files to `_build/cure/ebin/`. The stdlib provides 24 modules (~260 functions), including `Std.Core`, `Std.List`, `Std.Math`, `Std.String`, `Std.Pair`, `Std.Show`, `Std.Io`, `Std.System`, `Std.Map`, `Std.Set`, `Std.Option`, `Std.Functor`, the dependent-type helpers `Std.Equal` and `Std.Refine`, the v0.18.0 destructuring helpers in `Std.Match`, and the v0.19.0 additions `Std.Proof`, `Std.Gen`, and `Std.Iter`.

## Other CLI commands

```bash
cure version              # Show the Cure version
cure help                 # Show usage information
cure explain E011         # Show a detailed explanation for an error code
cure new myproject --lib  # Scaffold a new library project
cure deps                 # List dependencies
cure deps tree            # Inspect dependency graph
cure deps update          # Refresh Cure.lock
cure test --doctests      # Run tests, including doctests
cure repl                 # Multi-line REPL with :t, :doc, :holes, ...
cure watch lib/           # Recompile / check / test on every save
cure fmt lib/             # Format Cure sources
cure bench                # Run bench/**/*.cure benchmarks
```

## Editor setup

### Neovim (LSP)

Cure includes a Language Server Protocol implementation. Start it with `cure lsp` (or `mix cure.lsp` from the project directory). Configure Neovim to use it:

```lua
vim.api.nvim_create_autocmd("FileType", {
  pattern = "cure",
  callback = function()
    vim.lsp.start({
      name = "cure-lsp",
      cmd = { "cure", "lsp" },
      root_dir = vim.fs.root(0, { "mix.exs", ".git" }),
    })
  end,
})
```

You also need filetype detection. Add to your Neovim config:

```lua
vim.filetype.add({
  extension = {
    cure = "cure",
  },
})
```

The LSP provides:

- Real-time diagnostics (type errors, parse errors, exhaustiveness warnings, pattern coverage)
- Hover information with function signatures, inferred effects, unification traces, and hole goals
- Go-to-definition, `prepareRename` and rename
- Document symbols (hierarchical module / function outline)
- Workspace symbols
- Code actions (add missing match arms, did-you-mean suggestions)
- Completion (triggered by `.` and `:`)
- Inlay hints, signature help, code lenses, semantic tokens
- Formatting routed through the round-trip-tested `Cure.Compiler.Printer`

## MCP server for AI assistants

Cure provides an MCP (Model Context Protocol) server so AI coding assistants can compile, type-check, parse, and analyze Cure code directly:

```bash
mix cure.mcp
```

This starts a JSON-RPC 2.0 server over stdio, compatible with any MCP client (Claude, Warp, etc.). Available tools:

- `compile_cure` -- compile source, return module name or errors
- `parse_cure` -- parse source, return AST summary
- `type_check_cure` -- type-check source, return errors and warnings
- `analyze_fsm` -- analyze an FSM definition (states, transitions, verification)
- `validate_syntax` -- quick lex + parse validation
- `get_syntax_help` -- get help on a syntax topic
- `get_stdlib_docs` -- get documentation for a stdlib module

## Using from Elixir

You can also use Cure as a library from Elixir:

```elixir
# Compile and load into the running VM
{:ok, module} = Cure.Compiler.compile_and_load(source)
module.my_function(args)

# Compile with type checking
{:ok, module} = Cure.Compiler.compile_and_load(source, check_types: true)

# Compile to disk
{:ok, module, warnings} = Cure.Compiler.compile_file("hello.cure")
```

## Next steps

- [Language Guide](/language-guide) -- full syntax reference
- [Type System](/type-system) -- bidirectional checking, refinement types, SMT verification
- [Dependent Types](/type-system#dependent-types) -- Sigma, Pi, equality, implicit arguments, holes, totality
- [Finite State Machines](/finite-state-machines) -- first-class FSMs with compile-time verification
