# Cure Language Server Protocol (LSP) Implementation

This directory contains the Language Server Protocol implementation for the Cure programming language, enabling IDE features like autocomplete, diagnostics, go-to-definition, and more.

## Overview

The Cure LSP server provides the following features:

- **Diagnostics**: Real-time syntax and type error detection
  - Lexical and syntax errors
  - Dependent type checking
  - SMT-based constraint verification
  - Pattern exhaustiveness checking
  - Refinement type validation
- **Autocompletion**: Context-aware code completion for functions, FSMs, modules
- **Hover Information**: Type information and documentation on hover
- **Go to Definition**: Navigate to symbol definitions
- **Find References**: Find all references to a symbol
- **Document Symbols**: Outline view of document structure
- **Workspace Symbols**: Search symbols across the workspace

## Architecture

### Core Modules

- **cure_lsp_server.erl** (in `src/lsp/`): Main LSP server with JSON-RPC protocol handling
- **cure_lsp_analyzer.erl**: Integration with Cure compiler (lexer, parser, type checker)
- **cure_lsp_smt.erl**: SMT solver integration for constraint verification
- **cure_lsp_document.erl**: Document management and text synchronization
- **cure_lsp_symbols.erl**: Symbol table and workspace indexing

### Communication Flow

```
Editor (NeoVim/VSCode/etc)
    ↕ (JSON-RPC over stdin/stdout)
cure_lsp_server.erl (Protocol Handler)
    ↕
    ├→ cure_lsp_analyzer.erl (Lexer, Parser)
    ├→ cure_typechecker (Type checking)
    └→ cure_lsp_smt.erl (SMT verification)
         ├→ Pattern exhaustiveness
         ├→ Refinement types
         └→ Constraint solving
```

## Building

Build the LSP server along with the Cure compiler:

```bash
make lsp
```

This compiles all LSP modules to `_build/lsp/`.

## Running

The LSP server communicates via stdin/stdout using the Language Server Protocol:

```bash
./cure-lsp start
```

### Options

- `./cure-lsp start` - Start the LSP server (default)
- `./cure-lsp --version` - Show version information
- `./cure-lsp --help` - Show help message

## NeoVim Integration

### Prerequisites

1. Install [nvim-lspconfig](https://github.com/neovim/nvim-lspconfig):

```vim
" Using vim-plug
Plug 'neovim/nvim-lspconfig'

" Or using packer.nvim
use 'neovim/nvim-lspconfig'
```

2. (Optional) Install completion plugin:

```vim
Plug 'hrsh7th/nvim-cmp'
Plug 'hrsh7th/cmp-nvim-lsp'
```

### Configuration

Add the Cure LSP configuration to your NeoVim config. See `nvim-config-example.lua` for a complete example.

**Quick setup** (add to `~/.config/nvim/init.lua` or `~/.config/nvim/lua/lsp-config.lua`):

```lua
local lspconfig = require('lspconfig')
local configs = require('lspconfig.configs')

-- Define Cure LSP
if not configs.cure_lsp then
  configs.cure_lsp = {
    default_config = {
      cmd = { '/opt/Proyectos/Ammotion/cure/cure-lsp', 'start' },
      filetypes = { 'cure' },
      root_dir = function(fname)
        return lspconfig.util.find_git_ancestor(fname) or vim.fn.getcwd()
      end,
    },
  }
end

-- Setup Cure LSP with keybindings
lspconfig.cure_lsp.setup({
  on_attach = function(client, bufnr)
    -- Enable completion
    vim.api.nvim_buf_set_option(bufnr, 'omnifunc', 'v:lua.vim.lsp.omnifunc')
    
    -- Keybindings
    local opts = { noremap=true, silent=true, buffer=bufnr }
    vim.keymap.set('n', 'gd', vim.lsp.buf.definition, opts)
    vim.keymap.set('n', 'K', vim.lsp.buf.hover, opts)
    vim.keymap.set('n', 'gr', vim.lsp.buf.references, opts)
  end,
})

-- Recognize .cure files
vim.api.nvim_create_autocmd({"BufRead", "BufNewFile"}, {
  pattern = "*.cure",
  callback = function()
    vim.bo.filetype = "cure"
  end,
})
```

### Keybindings

Default LSP keybindings in the example configuration:

- `gd` - Go to definition
- `gD` - Go to declaration
- `K` - Hover information
- `gi` - Go to implementation
- `gr` - Find references
- `<space>rn` - Rename symbol
- `<space>ca` - Code actions
- `<C-k>` - Signature help

## Development

### Testing the LSP Server

Start an interactive Erlang shell with LSP modules loaded:

```bash
make lsp-shell
```

Test the analyzer:

```erlang
Text = <<"module example\nexport main/0\n\ndef main() -> print(\"Hello\")\n">>.
cure_lsp_analyzer:analyze(Text).
```

### Debugging

The LSP server writes debug information to stderr. When running in NeoVim, you can view logs:

```vim
:LspLog
```

Or check the NeoVim LSP client status:

```vim
:LspInfo
```

### Adding New Features

To add a new LSP feature:

1. Add the capability in `handle_initialize/3` in `cure_lsp.erl`
2. Add a handler function in `process_message/2`
3. Implement the analysis logic in `cure_lsp_analyzer.erl`
4. Update the symbol table in `cure_lsp_symbols.erl` if needed

## Advanced Features

### Type Checking Integration

The LSP runs the full Cure type checker on every document change, providing:

- **Dependent type verification**: Validates constraints on type parameters
- **Generic type resolution**: Ensures type parameters are correctly instantiated
- **FSM handler checking**: Verifies FSM event handler signatures
- **Function signature matching**: Checks parameter and return types

See [LSP_SMT_INTEGRATION.md](./LSP_SMT_INTEGRATION.md) for details.

### SMT Solver Integration

The LSP integrates with Z3/CVC5 SMT solvers for advanced verification:

- **Pattern exhaustiveness**: Detects missing pattern match cases
- **Refinement types**: Validates type predicates (e.g., `n > 0`)
- **Constraint solving**: Proves or disproves dependent type constraints
- **Counter-examples**: Generates examples when constraints fail

#### Example: Pattern Exhaustiveness

```cure
def describe(x: Option(Int)) -> String do
    match x do
        | Some(n) -> "Has value"
        // Warning: Missing case for None
    end
end
```

#### Example: Refinement Types

```cure
type PositiveInt = Int when n > 0

def safe_div(x: Int, y: PositiveInt) -> Int do
    x / y  // OK: y is guaranteed > 0
end

safe_div(10, -5)  // Error: Refinement type violated
```

## Dependencies

The LSP server requires:

- **Erlang/OTP 27+**: For native `json` module support
- **Cure compiler**: Lexer, parser, and type checker
- **cure_smt_solver**: SMT solver integration (Z3 or CVC5 recommended)

No external Erlang dependencies are needed - the LSP uses Erlang's built-in `json` module for JSON encoding/decoding.

### Optional: SMT Solver

For enhanced verification features, install Z3 or CVC5:

```bash
# Ubuntu/Debian
sudo apt install z3

# macOS
brew install z3

# Or download from https://github.com/Z3Prover/z3/releases
```

The LSP will automatically detect available solvers and use them for advanced checks.

## Protocol Implementation Status

### Implemented

- ✅ `initialize` / `initialized`
- ✅ `shutdown` / `exit`
- ✅ `textDocument/didOpen`
- ✅ `textDocument/didChange` (incremental sync)
- ✅ `textDocument/didClose`
- ✅ `textDocument/publishDiagnostics`
- ✅ Document management
- ✅ Symbol extraction

### Partially Implemented

- 🚧 `textDocument/completion` (basic structure, needs full implementation)
- 🚧 `textDocument/hover` (basic structure, needs full implementation)
- 🚧 `textDocument/definition` (basic structure, needs full implementation)
- 🚧 `textDocument/references` (basic structure, needs full implementation)
- 🚧 `textDocument/documentSymbol` (basic structure, needs full implementation)

### Planned

- ⬜ `textDocument/formatting`
- ⬜ `textDocument/rangeFormatting`
- ⬜ `textDocument/codeAction`
- ⬜ `textDocument/rename`
- ⬜ `workspace/symbol`
- ⬜ `textDocument/semanticTokens`

## Known Issues

1. **Incremental sync**: May have edge cases with multi-line edits
2. **Symbol resolution**: Cross-module references need workspace indexing
3. **Type information**: Hover info needs integration with type inference
4. **Completion**: Currently returns basic completions, needs context-aware filtering

## Contributing

To contribute to the LSP implementation:

1. Follow Erlang coding conventions (use `rebar3 fmt`)
2. Test with real Cure code examples
3. Ensure compatibility with the LSP specification
4. Update documentation for new features

## Resources

- [Language Server Protocol Specification](https://microsoft.github.io/language-server-protocol/)
- [NeoVim LSP Documentation](https://neovim.io/doc/user/lsp.html)
- [Cure Language Documentation](../README.md)
