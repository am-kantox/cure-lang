# Cure LSP Quick Start Guide

Get the Cure Language Server Protocol running in NeoVim in 5 minutes.

## Step 1: Build the LSP Server

```bash
cd /opt/Proyectos/Ammotion/cure
make lsp
```

Verify it works:
```bash
./cure-lsp --version
```

## Step 2: Configure NeoVim

Add to your NeoVim configuration (`~/.config/nvim/init.lua`):

```lua
local lspconfig = require('lspconfig')
local configs = require('lspconfig.configs')

-- Define Cure LSP
if not configs.cure_lsp then
  configs.cure_lsp = {
    default_config = {
      cmd = { '/opt/Proyectos/Ammotion/cure/cure-lsp', 'start' },
      filetypes = { 'cure' },
      root_dir = lspconfig.util.find_git_ancestor,
    },
  }
end

-- Setup Cure LSP
lspconfig.cure_lsp.setup({
  on_attach = function(client, bufnr)
    vim.api.nvim_buf_set_option(bufnr, 'omnifunc', 'v:lua.vim.lsp.omnifunc')
    
    local opts = { noremap=true, silent=true, buffer=bufnr }
    vim.keymap.set('n', 'gd', vim.lsp.buf.definition, opts)
    vim.keymap.set('n', 'K', vim.lsp.buf.hover, opts)
    vim.keymap.set('n', 'gr', vim.lsp.buf.references, opts)
  end,
})

-- Recognize .cure files
vim.filetype.add({
  extension = {
    cure = 'cure',
  },
})
```

## Step 3: Test It

1. Open a `.cure` file in NeoVim:
   ```bash
   nvim examples/simple.cure
   ```

2. Check LSP status:
   ```vim
   :LspInfo
   ```

3. You should see "cure_lsp: attached" and the client running.

## Step 4: Use LSP Features

- **Diagnostics**: Syntax errors will appear automatically
- **Go to definition**: Press `gd` on a function name
- **Hover info**: Press `K` to see type information
- **Find references**: Press `gr` to find all usages
- **Auto-complete**: Use `<C-x><C-o>` or your completion plugin

## Troubleshooting

### LSP not attaching
Check the LSP log:
```vim
:LspLog
```

Make sure the cure-lsp path is correct in your config.

### No diagnostics appearing
The LSP may be waiting for you to save the file. Try `:w` to save.

## Next Steps

- Read the full [README.md](README.md) for detailed documentation
- Check [nvim-config-example.lua](nvim-config-example.lua) for advanced configuration
- Contribute to the LSP by implementing additional features!

## Key Files

- `cure_lsp.erl` - Main LSP server
- `cure_lsp_analyzer.erl` - Compiler integration
- `cure_lsp_document.erl` - Document management
- `cure_lsp_symbols.erl` - Symbol table
- `cure-lsp` - Executable script

## Support

For issues or questions:
1. Check `:LspLog` in NeoVim for errors
2. Run `./cure-lsp start` manually to see stderr output
3. Review the LSP specification: https://microsoft.github.io/language-server-protocol/
