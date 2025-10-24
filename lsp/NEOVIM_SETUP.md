# Cure LSP - NeoVim Setup and Testing Guide

Complete guide to set up and test the Cure Language Server in NeoVim.

## Prerequisites

1. **NeoVim** 0.8+ with Lua support
2. **nvim-lspconfig** plugin installed
3. **Cure compiler** and LSP built (`make lsp`)

### Install nvim-lspconfig

Using **lazy.nvim**:
```lua
{
  'neovim/nvim-lspconfig',
  dependencies = {
    'hrsh7th/nvim-cmp',         -- Optional: completion
    'hrsh7th/cmp-nvim-lsp',     -- Optional: LSP completion source
  }
}
```

Using **packer.nvim**:
```lua
use 'neovim/nvim-lspconfig'
use 'hrsh7th/nvim-cmp'        -- Optional
use 'hrsh7th/cmp-nvim-lsp'    -- Optional
```

Using **vim-plug**:
```vim
Plug 'neovim/nvim-lspconfig'
Plug 'hrsh7th/nvim-cmp'
Plug 'hrsh7th/cmp-nvim-lsp'
```

## Configuration

### Minimal Setup

Add to `~/.config/nvim/init.lua` or `~/.config/nvim/lua/lsp/cure.lua`:

```lua
local lspconfig = require('lspconfig')
local configs = require('lspconfig.configs')

-- Define Cure LSP configuration
if not configs.cure_lsp then
  configs.cure_lsp = {
    default_config = {
      cmd = { '/opt/Proyectos/Ammotion/cure/cure-lsp', 'start' },
      filetypes = { 'cure' },
      root_dir = function(fname)
        return lspconfig.util.find_git_ancestor(fname) or vim.fn.getcwd()
      end,
      settings = {},
    },
  }
end

-- Setup Cure LSP with basic keybindings
lspconfig.cure_lsp.setup({
  on_attach = function(client, bufnr)
    -- Enable completion triggered by <c-x><c-o>
    vim.api.nvim_buf_set_option(bufnr, 'omnifunc', 'v:lua.vim.lsp.omnifunc')
    
    -- Keybindings
    local opts = { noremap = true, silent = true, buffer = bufnr }
    
    vim.keymap.set('n', 'gD', vim.lsp.buf.declaration, opts)
    vim.keymap.set('n', 'gd', vim.lsp.buf.definition, opts)
    vim.keymap.set('n', 'K', vim.lsp.buf.hover, opts)
    vim.keymap.set('n', 'gi', vim.lsp.buf.implementation, opts)
    vim.keymap.set('n', 'gr', vim.lsp.buf.references, opts)
    vim.keymap.set('n', '<C-k>', vim.lsp.buf.signature_help, opts)
    vim.keymap.set('n', '<space>D', vim.lsp.buf.type_definition, opts)
    vim.keymap.set('n', '<space>rn', vim.lsp.buf.rename, opts)
    vim.keymap.set('n', '<space>ca', vim.lsp.buf.code_action, opts)
    
    print("Cure LSP attached to buffer " .. bufnr)
  end,
  capabilities = require('cmp_nvim_lsp').default_capabilities(), -- Optional: for nvim-cmp
})

-- Recognize .cure files as 'cure' filetype
vim.filetype.add({
  extension = {
    cure = 'cure',
  },
})
```

### Full Setup with Diagnostics and Completion

For a more complete setup, add this configuration:

```lua
local lspconfig = require('lspconfig')
local configs = require('lspconfig.configs')

-- Configure diagnostics appearance
vim.diagnostic.config({
  virtual_text = {
    prefix = '●',
    source = 'always',
  },
  signs = true,
  underline = true,
  update_in_insert = false,
  severity_sort = true,
})

-- Define diagnostic signs
local signs = { Error = " ", Warn = " ", Hint = " ", Info = " " }
for type, icon in pairs(signs) do
  local hl = "DiagnosticSign" .. type
  vim.fn.sign_define(hl, { text = icon, texthl = hl, numhl = hl })
end

-- Cure LSP configuration
if not configs.cure_lsp then
  configs.cure_lsp = {
    default_config = {
      cmd = { '/opt/Proyectos/Ammotion/cure/cure-lsp', 'start' },
      filetypes = { 'cure' },
      root_dir = function(fname)
        return lspconfig.util.find_git_ancestor(fname) or vim.fn.getcwd()
      end,
      settings = {},
      single_file_support = true,
    },
  }
end

-- Setup with enhanced on_attach
lspconfig.cure_lsp.setup({
  on_attach = function(client, bufnr)
    vim.api.nvim_buf_set_option(bufnr, 'omnifunc', 'v:lua.vim.lsp.omnifunc')
    
    local opts = { noremap = true, silent = true, buffer = bufnr }
    
    -- Navigation
    vim.keymap.set('n', 'gD', vim.lsp.buf.declaration, opts)
    vim.keymap.set('n', 'gd', vim.lsp.buf.definition, opts)
    vim.keymap.set('n', 'gi', vim.lsp.buf.implementation, opts)
    vim.keymap.set('n', 'gr', vim.lsp.buf.references, opts)
    vim.keymap.set('n', 'go', vim.lsp.buf.type_definition, opts)
    
    -- Information
    vim.keymap.set('n', 'K', vim.lsp.buf.hover, opts)
    vim.keymap.set('n', '<C-k>', vim.lsp.buf.signature_help, opts)
    
    -- Diagnostics
    vim.keymap.set('n', '[d', vim.diagnostic.goto_prev, opts)
    vim.keymap.set('n', ']d', vim.diagnostic.goto_next, opts)
    vim.keymap.set('n', '<space>e', vim.diagnostic.open_float, opts)
    vim.keymap.set('n', '<space>q', vim.diagnostic.setloclist, opts)
    
    -- Actions
    vim.keymap.set('n', '<space>rn', vim.lsp.buf.rename, opts)
    vim.keymap.set('n', '<space>ca', vim.lsp.buf.code_action, opts)
    
    -- Formatting
    vim.keymap.set('n', '<space>f', function()
      vim.lsp.buf.format({ async = true })
    end, opts)
    
    -- Document symbols
    vim.keymap.set('n', '<space>ds', vim.lsp.buf.document_symbol, opts)
    
    print("✓ Cure LSP attached to buffer " .. bufnr)
  end,
  capabilities = require('cmp_nvim_lsp').default_capabilities(),
})

-- Filetype detection
vim.filetype.add({
  extension = {
    cure = 'cure',
  },
})

-- Auto-commands for Cure files
vim.api.nvim_create_autocmd('FileType', {
  pattern = 'cure',
  callback = function()
    vim.opt_local.commentstring = '# %s'
    vim.opt_local.shiftwidth = 2
    vim.opt_local.tabstop = 2
    vim.opt_local.expandtab = true
  end,
})
```

## Testing the Setup

### 1. Build the LSP Server

```bash
cd /opt/Proyectos/Ammotion/cure
make clean
make lsp
```

Verify the build:
```bash
./cure-lsp --version
# Should output: Cure Language Server version 0.1.0
```

### 2. Test LSP Manually

Before testing in NeoVim, verify the LSP server works:

```bash
cd /opt/Proyectos/Ammotion/cure
./cure-lsp start
```

Then send a test message (Ctrl+D to exit):
```json
Content-Length: 127

{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{},"rootUri":"file:///opt/Proyectos/Ammotion/cure"}}
```

You should see a JSON response with server capabilities.

### 3. Test in NeoVim

Open a Cure file:
```bash
nvim examples/vector_test.cure
```

#### Check LSP Status

Inside NeoVim:
```vim
:LspInfo
```

You should see:
```
 Language client log: /home/am/.local/state/nvim/lsp.log
 Detected filetype:   cure

 1 client(s) attached to this buffer: 

 Client: cure_lsp (id: 1, bufnr: [1])
  filetypes:       cure
  autostart:       true
  root directory:  /opt/Proyectos/Ammotion/cure
  cmd:             /opt/Proyectos/Ammotion/cure/cure-lsp start
```

#### Check for Diagnostics

If there's a syntax error, you should see diagnostics appear. Try adding invalid syntax:

```cure
module Test do
  thisisnotvalid
end
```

Save the file (`:w`). Diagnostics should appear as virtual text and in the sign column.

#### Test Features

1. **Hover**: Move cursor to a function name and press `K`
   - Should show type information in a floating window

2. **Go to Definition**: Move cursor to a function call and press `gd`
   - Should jump to the function definition

3. **Find References**: On a function name, press `gr`
   - Should show all references in a quickfix list

4. **Completion**: In insert mode, type part of a function name and press `<C-x><C-o>`
   - Should show completion suggestions

5. **Document Symbols**: Press `<space>ds`
   - Should show an outline of the document

### 4. Debugging

#### View LSP Logs

```vim
:LspLog
```

This opens the LSP log file showing all communication between NeoVim and the LSP server.

#### Check LSP Server Output

Run the LSP manually to see stderr output:
```bash
cd /opt/Proyectos/Ammotion/cure
./cure-lsp start 2> lsp-debug.log
```

Then open a Cure file in NeoVim and check `lsp-debug.log`.

#### Enable Verbose Logging

Add to your NeoVim config before the LSP setup:
```lua
vim.lsp.set_log_level("debug")
```

#### Test Analyzer Directly

Test the analyzer in Erlang shell:
```bash
cd /opt/Proyectos/Ammotion/cure
erl -pa _build/ebin -pa _build/lsp
```

Then:
```erlang
{ok, Text} = file:read_file("examples/vector_test.cure").
cure_lsp_analyzer:analyze(Text).
% Should return: []  (no diagnostics if file is valid)

cure_lsp_analyzer:extract_symbols(Text).
% Should return list of symbols in the file
```

## Common Issues and Solutions

### Issue: "cure_lsp not found"

**Solution**: Check the path in your LSP config matches the cure-lsp location:
```lua
cmd = { '/opt/Proyectos/Ammotion/cure/cure-lsp', 'start' }
```

Update to your actual path.

### Issue: "Client 1 quit with exit code 1"

**Solution**: 
1. Check if the LSP builds correctly: `make lsp`
2. Run `./cure-lsp --version` to verify it works
3. Check `:LspLog` for specific errors

### Issue: No diagnostics appearing

**Causes**:
- File not saved (try `:w`)
- LSP not attached (check `:LspInfo`)
- Parser errors (check `:LspLog`)

**Solution**:
```vim
:LspRestart
```

### Issue: "Unexpected token identifier" on valid code

**Solution**: This was a bug that has been fixed. Make sure you've rebuilt the LSP:
```bash
make clean
make lsp
```

## Keybinding Reference

With the full setup, these keybindings are available in `.cure` files:

| Key | Action |
|-----|--------|
| `gD` | Go to declaration |
| `gd` | Go to definition |
| `gi` | Go to implementation |
| `gr` | Find references |
| `go` | Go to type definition |
| `K` | Hover information |
| `<C-k>` | Signature help |
| `[d` | Previous diagnostic |
| `]d` | Next diagnostic |
| `<space>e` | Show diagnostic float |
| `<space>q` | Show diagnostic list |
| `<space>rn` | Rename symbol |
| `<space>ca` | Code action |
| `<space>f` | Format document |
| `<space>ds` | Document symbols |

## Test File

Create a test file `test.cure` with this content:

```cure
module Test do
  export [main/0, greet/1]
  
  import Std.Core [print/1]
  
  def main(): Bool =
    greet("World")
    true
  end
  
  def greet(name: String): Unit =
    print("Hello, " ++ name)
  end
end
```

Open in NeoVim and test:
1. Hover over `greet` - should show function signature
2. Press `gd` on `greet("World")` - should jump to definition
3. Press `gr` on `def greet` - should find the call site
4. Check `:LspInfo` - should show attached

## Next Steps

- Check [README.md](README.md) for LSP architecture details
- See [LSP_FEATURES.md](LSP_FEATURES.md) for feature status
- Contribute improvements to the LSP implementation!
