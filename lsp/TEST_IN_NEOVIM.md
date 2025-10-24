# Test Cure LSP in NeoVim - Quick Guide

## Prerequisites Check

```bash
# 1. Verify LSP is built
./cure-lsp --version
# Should output: Cure Language Server version 0.1.0

# 2. Run automated tests
./test-lsp.sh
# Should show 3 symbols found, no diagnostics
```

## NeoVim Configuration

Add to `~/.config/nvim/init.lua` (or create `~/.config/nvim/lua/lsp/cure.lua`):

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
      settings = {},
    },
  }
end

-- Setup with keybindings
lspconfig.cure_lsp.setup({
  on_attach = function(client, bufnr)
    print("✓ Cure LSP attached to buffer " .. bufnr)
    
    local opts = { noremap = true, silent = true, buffer = bufnr }
    vim.keymap.set('n', 'gd', vim.lsp.buf.definition, opts)
    vim.keymap.set('n', 'K', vim.lsp.buf.hover, opts)
    vim.keymap.set('n', 'gr', vim.lsp.buf.references, opts)
    vim.keymap.set('n', '[d', vim.diagnostic.goto_prev, opts)
    vim.keymap.set('n', ']d', vim.diagnostic.goto_next, opts)
  end,
})

-- Recognize .cure files
vim.filetype.add({
  extension = { cure = 'cure' },
})
```

## Testing Steps

### 1. Open a Cure file
```bash
nvim examples/vector_test.cure
```

### 2. Check LSP status
Inside NeoVim:
```vim
:LspInfo
```

**Expected output:**
```
 Language client log: ~/.local/state/nvim/lsp.log
 Detected filetype:   cure

 1 client(s) attached to this buffer: 

 Client: cure_lsp (id: 1, bufnr: [1])
  filetypes:       cure
  autostart:       true
  root directory:  /opt/Proyectos/Ammotion/cure
  cmd:             /opt/Proyectos/Ammotion/cure/cure-lsp start
```

### 3. View LSP logs (if issues)
```vim
:LspLog
```

Look for:
- ✓ "Starting Cure Language Server..."
- ✓ "Cure LSP server started"
- ✗ Any error messages

### 4. Test features

1. **Document Symbols**: `:lua vim.lsp.buf.document_symbol()`
   - Should show module and function list

2. **Hover**: Move cursor to function name, press `K`
   - Should show type information

3. **Go to Definition**: Move cursor to function call, press `gd`
   - Should jump to definition

## Troubleshooting

### Issue: "Client 1 quit with exit code 1"

**Check build:**
```bash
cd /opt/Proyectos/Ammotion/cure
make clean
make lsp
./cure-lsp --version
```

**Check logs:**
```vim
:LspLog
```

Look for specific error messages.

### Issue: LSP not attaching

**Verify file type:**
```vim
:set filetype?
```
Should show `filetype=cure`

**Force attach:**
```vim
:LspRestart
```

### Issue: No response from LSP

**Check if server is running:**
```bash
ps aux | grep cure-lsp
```

**Restart NeoVim:**
Sometimes a clean restart helps after config changes.

## Debug Mode

Enable verbose logging in your NeoVim config:

```lua
-- Add before lspconfig.cure_lsp.setup()
vim.lsp.set_log_level("debug")
```

Then check `:LspLog` for detailed messages.

## Manual Testing

Test the LSP server manually:

```bash
cd /opt/Proyectos/Ammotion/cure

# Start LSP (will wait for input)
./cure-lsp start

# In another terminal, check if it's running
ps aux | grep cure-lsp
```

## Success Indicators

- ✓ `:LspInfo` shows "cure_lsp" attached
- ✓ Console message: "✓ Cure LSP attached to buffer X"
- ✓ No errors in `:LspLog`
- ✓ `K` on function shows hover info
- ✓ Document symbols work

## Common Commands

| Command | Action |
|---------|--------|
| `:LspInfo` | Check LSP status |
| `:LspLog` | View LSP logs |
| `:LspRestart` | Restart LSP client |
| `:LspStop` | Stop LSP client |
| `:LspStart cure_lsp` | Start Cure LSP |

## Next Steps

Once working:
- See [NEOVIM_SETUP.md](NEOVIM_SETUP.md) for full configuration
- Check [README.md](README.md) for LSP architecture
- Review [CHANGELOG_LSP.md](CHANGELOG_LSP.md) for recent changes
