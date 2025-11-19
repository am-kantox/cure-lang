# Cure MCP Server - LunarVim Integration

This guide explains how to use the Cure MCP server within LunarVim via MCPHub.

## What is MCPHub?

MCPHub is a Neovim/LunarVim plugin that integrates Model Context Protocol servers directly into your editor, enabling AI-assisted development with language-specific tools.

## Installation

The Cure MCP server has been added to your LunarVim configuration automatically.

### Verify Installation

1. **Open LunarVim:**
   ```bash
   lvim
   ```

2. **Check MCPHub is loaded:**
   ```vim
   :MCPHub
   ```
   
   You should see the MCPHub interface. The Cure server should be listed.

3. **Check server status:**
   ```vim
   :lua print(vim.inspect(require("mcphub").get_servers()))
   ```

## Configuration

Your LunarVim config (`~/.config/lvim/config.lua`) now includes:

```lua
{
  "ravitemer/mcphub.nvim",
  config = function()
    require("mcphub").setup({
      servers = {
        cure = {
          command = "/opt/Proyectos/Ammotion/cure/mcp/cure-mcp-server.sh",
          args = {},
          stdio = true,
          description = "Cure language MCP server - compilation, type-checking, FSM analysis",
        }
      }
    })
  end,
}
```

Additionally, a servers configuration file was created at:
`~/.config/mcp-hub/servers.json`

## Usage

### Key Bindings

Default MCPHub key bindings in your LunarVim config:

- **`<leader>Mm`** - Open MCPHub interface
- **`@M`** (in visual mode) - MCPHub with selected text

Where `<leader>` is typically `<Space>`.

### Using MCPHub

1. **Open MCPHub:**
   ```
   <Space>Mm
   ```
   or
   ```
   :MCPHub
   ```

2. **Select the Cure server** from the list

3. **Choose a tool:**
   - `compile_cure` - Compile Cure file
   - `parse_cure` - Parse Cure code
   - `type_check_cure` - Type-check code
   - `validate_syntax` - Validate syntax
   - `get_ast` - Get AST representation
   - `analyze_fsm` - Analyze FSM definitions
   - `get_syntax_help` - Get syntax help
   - `get_examples` - Get code examples
   - `get_stdlib_docs` - Get stdlib documentation

### Example Workflows

#### Workflow 1: Validate Current Buffer

1. Open a `.cure` file in LunarVim
2. Press `<Space>Mm` to open MCPHub
3. Select "cure" server
4. Select "validate_syntax" tool
5. The current buffer content will be validated

#### Workflow 2: Get FSM Syntax Help

1. Press `<Space>Mm`
2. Select "cure" server
3. Select "get_syntax_help" tool
4. Choose "fsm" topic
5. FSM syntax reference will be displayed

#### Workflow 3: Check Selected Code

1. In a `.cure` file, visually select code (Visual mode)
2. Press `@M`
3. Select "cure" server
4. Select "type_check_cure" or "validate_syntax"
5. Selected code will be analyzed

#### Workflow 4: Compile Current File

1. Open a `.cure` file
2. Press `<Space>Mm`
3. Select "cure" server
4. Select "compile_cure" tool
5. Provide file path when prompted
6. Compilation results will be shown

## Available Tools

### Compilation Tools

**`compile_cure`**
- Compiles Cure source to BEAM bytecode
- **Input:** `file_path` (required), `output_dir` (optional)
- **Output:** List of generated BEAM files or errors

**`parse_cure`**
- Parses Cure code and returns AST
- **Input:** `code` (required)
- **Output:** AST summary

**`type_check_cure`**
- Type-checks Cure code
- **Input:** `code` (required)
- **Output:** Type checking results or errors

**`validate_syntax`**
- Quick syntax validation
- **Input:** `code` (required)
- **Output:** Valid/Invalid status

**`get_ast`**
- Get detailed AST representation
- **Input:** `code` (required), `pretty_print` (optional, default: true)
- **Output:** Formatted AST

### FSM Tools

**`analyze_fsm`**
- Analyzes FSM definitions
- **Input:** `code` (required)
- **Output:** FSM structure (states, transitions, initial state)

### Documentation Tools

**`get_syntax_help`**
- Get syntax reference
- **Input:** `topic` (required: functions, types, fsm, typeclasses, pattern_matching, modules, records, all)
- **Output:** Syntax examples and explanations

**`get_examples`**
- Get code examples
- **Input:** `category` (required: basics, fsm, typeclasses, advanced, all)
- **Output:** Commented example code

**`get_stdlib_docs`**
- Get standard library docs
- **Input:** `module` (required: Std.List, Std.Io, Std.Fsm, Std.Option, Std.Result, all)
- **Output:** Function signatures and usage examples

## Integration with Cure LSP

The MCP server complements the Cure LSP (Language Server Protocol) that's also configured in your LunarVim:

- **LSP:** Real-time diagnostics, go-to-definition, hover, completion
- **MCP:** On-demand compilation, documentation lookup, FSM analysis, examples

They work together to provide comprehensive Cure language support.

## Troubleshooting

### Server Not Found in MCPHub

1. Restart LunarVim completely
2. Check if the server script is executable:
   ```bash
   ls -la /opt/Proyectos/Ammotion/cure/mcp/cure-mcp-server.sh
   chmod +x /opt/Proyectos/Ammotion/cure/mcp/cure-mcp-server.sh
   ```

3. Test the server manually:
   ```bash
   echo '{"jsonrpc":"2.0","method":"initialize","params":{},"id":1}' | \
     /opt/Proyectos/Ammotion/cure/mcp/cure-mcp-server.sh
   ```

### Tools Not Working

1. Ensure Cure compiler is built:
   ```bash
   cd /opt/Proyectos/Ammotion/cure
   make all
   ```

2. Check dependencies:
   ```bash
   rebar3 get-deps
   rebar3 compile
   ```

3. Check LunarVim logs:
   ```vim
   :messages
   ```

### MCPHub Not Responding

1. Check if mcp-hub is installed:
   ```bash
   npm list -g mcp-hub
   ```

2. Reinstall if needed:
   ```bash
   npm install -g mcp-hub@latest
   ```

3. Sync LunarVim plugins:
   ```vim
   :Lazy sync
   ```

## Advanced Configuration

### Custom Tool Shortcuts

Add custom shortcuts to your LunarVim config:

```lua
-- Add to ~/.config/lvim/config.lua

-- Quick Cure validation
vim.keymap.set('n', '<leader>cv', function()
  local bufnr = vim.api.nvim_get_current_buf()
  local lines = vim.api.nvim_buf_get_lines(bufnr, 0, -1, false)
  local code = table.concat(lines, "\n")
  
  -- Call MCPHub with cure server validate_syntax tool
  require('mcphub').call_tool('cure', 'validate_syntax', { code = code })
end, { desc = "Cure: Validate syntax" })

-- Quick FSM analysis
vim.keymap.set('n', '<leader>cf', function()
  local bufnr = vim.api.nvim_get_current_buf()
  local lines = vim.api.nvim_buf_get_lines(bufnr, 0, -1, false)
  local code = table.concat(lines, "\n")
  
  require('mcphub').call_tool('cure', 'analyze_fsm', { code = code })
end, { desc = "Cure: Analyze FSM" })

-- Get Cure syntax help
vim.keymap.set('n', '<leader>ch', function()
  vim.ui.select(
    {'functions', 'types', 'fsm', 'typeclasses', 'pattern_matching', 'modules', 'records', 'all'},
    { prompt = 'Select syntax topic:' },
    function(choice)
      if choice then
        require('mcphub').call_tool('cure', 'get_syntax_help', { topic = choice })
      end
    end
  )
end, { desc = "Cure: Get syntax help" })
```

### Auto-validation on Save

Add automatic syntax validation when saving `.cure` files:

```lua
-- Add to ~/.config/lvim/config.lua

vim.api.nvim_create_autocmd("BufWritePost", {
  pattern = "*.cure",
  callback = function()
    local bufnr = vim.api.nvim_get_current_buf()
    local lines = vim.api.nvim_buf_get_lines(bufnr, 0, -1, false)
    local code = table.concat(lines, "\n")
    
    require('mcphub').call_tool('cure', 'validate_syntax', { code = code })
  end,
})
```

### Integration with Which-Key

Add MCPHub tools to Which-Key menu:

```lua
-- Add to ~/.config/lvim/config.lua

lvim.builtin.which_key.mappings["c"] = {
  name = "Cure",
  v = { "<cmd>lua require('mcphub').call_tool('cure', 'validate_syntax', { code = vim.api.nvim_buf_get_lines(0, 0, -1, false) })<cr>", "Validate syntax" },
  f = { "<cmd>lua require('mcphub').call_tool('cure', 'analyze_fsm', { code = vim.api.nvim_buf_get_lines(0, 0, -1, false) })<cr>", "Analyze FSM" },
  h = { "<cmd>lua vim.ui.select({'functions', 'types', 'fsm'}, {}, function(c) require('mcphub').call_tool('cure', 'get_syntax_help', {topic=c}) end)<cr>", "Syntax help" },
  e = { "<cmd>lua vim.ui.select({'basics', 'fsm', 'typeclasses'}, {}, function(c) require('mcphub').call_tool('cure', 'get_examples', {category=c}) end)<cr>", "Get examples" },
}
```

## Benefits of MCP Integration

### For Development
- **Quick validation** without leaving the editor
- **In-editor documentation** lookup
- **Example code** access
- **FSM analysis** on-demand

### For Learning
- **Interactive syntax help**
- **Instant code validation**
- **Live examples**
- **Standard library exploration**

### Workflow Enhancement
- **No context switching** - everything in LunarVim
- **Fast feedback** - instant compilation results
- **Integrated tools** - MCP + LSP working together
- **Customizable** - add your own shortcuts and workflows

## See Also

- [MCPHub Plugin](https://github.com/ravitemer/mcphub.nvim)
- [MCP Protocol](https://modelcontextprotocol.io/)
- [Cure MCP Server Documentation](README.md)
- [LunarVim Documentation](https://www.lunarvim.org/)

## Support

For issues with:
- **MCP Server:** See [QUICKSTART.md](QUICKSTART.md) or [README.md](README.md)
- **LunarVim Integration:** Check LunarVim logs with `:messages`
- **MCPHub Plugin:** Visit [MCPHub repository](https://github.com/ravitemer/mcphub.nvim)
