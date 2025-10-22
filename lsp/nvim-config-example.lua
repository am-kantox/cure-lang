-- Cure Language Server Configuration for NeoVim
-- Add this to your NeoVim configuration (e.g., ~/.config/nvim/lua/lsp-config.lua)

local lspconfig = require('lspconfig')
local configs = require('lspconfig.configs')

-- Define Cure LSP if not already defined
if not configs.cure_lsp then
  configs.cure_lsp = {
    default_config = {
      cmd = { '/opt/Proyectos/Ammotion/cure/cure-lsp', 'start' },
      filetypes = { 'cure' },
      root_dir = function(fname)
        return lspconfig.util.find_git_ancestor(fname) or vim.fn.getcwd()
      end,
      settings = {},
      init_options = {},
      capabilities = vim.lsp.protocol.make_client_capabilities(),
    },
  }
end

-- Setup Cure LSP
lspconfig.cure_lsp.setup({
  on_attach = function(client, bufnr)
    -- Enable completion triggered by <c-x><c-o>
    vim.api.nvim_buf_set_option(bufnr, 'omnifunc', 'v:lua.vim.lsp.omnifunc')

    -- Key mappings for LSP functions
    local bufopts = { noremap=true, silent=true, buffer=bufnr }
    
    vim.keymap.set('n', 'gD', vim.lsp.buf.declaration, bufopts)
    vim.keymap.set('n', 'gd', vim.lsp.buf.definition, bufopts)
    vim.keymap.set('n', 'K', vim.lsp.buf.hover, bufopts)
    vim.keymap.set('n', 'gi', vim.lsp.buf.implementation, bufopts)
    vim.keymap.set('n', '<C-k>', vim.lsp.buf.signature_help, bufopts)
    vim.keymap.set('n', '<space>wa', vim.lsp.buf.add_workspace_folder, bufopts)
    vim.keymap.set('n', '<space>wr', vim.lsp.buf.remove_workspace_folder, bufopts)
    vim.keymap.set('n', '<space>wl', function()
      print(vim.inspect(vim.lsp.buf.list_workspace_folders()))
    end, bufopts)
    vim.keymap.set('n', '<space>D', vim.lsp.buf.type_definition, bufopts)
    vim.keymap.set('n', '<space>rn', vim.lsp.buf.rename, bufopts)
    vim.keymap.set('n', '<space>ca', vim.lsp.buf.code_action, bufopts)
    vim.keymap.set('n', 'gr', vim.lsp.buf.references, bufopts)
    vim.keymap.set('n', '<space>f', function() 
      vim.lsp.buf.format { async = true } 
    end, bufopts)

    -- Auto-format on save (optional)
    -- vim.api.nvim_create_autocmd("BufWritePre", {
    --   buffer = bufnr,
    --   callback = function()
    --     vim.lsp.buf.format { async = false }
    --   end
    -- })

    print("Cure LSP attached to buffer " .. bufnr)
  end,
  
  flags = {
    debounce_text_changes = 150,
  },
  
  capabilities = require('cmp_nvim_lsp').default_capabilities(
    vim.lsp.protocol.make_client_capabilities()
  ),
})

-- Optional: Add file type detection for .cure files
vim.api.nvim_create_autocmd({"BufRead", "BufNewFile"}, {
  pattern = "*.cure",
  callback = function()
    vim.bo.filetype = "cure"
  end,
})

-- Optional: Add syntax highlighting rules for Cure
-- (This is a basic example - you'd want to expand this)
vim.api.nvim_create_autocmd("FileType", {
  pattern = "cure",
  callback = function()
    -- Keywords
    vim.cmd([[syntax keyword cureKeyword module export import def fsm state transition match if then else let in type]]
    vim.cmd([[syntax keyword cureType Int String Bool Float List Vector]]
    vim.cmd([[syntax keyword cureBuiltin print length map filter fold]]
    
    -- Comments
    vim.cmd([[syntax match cureComment "#.*$"]])
    
    -- Strings
    vim.cmd([[syntax region cureString start='"' end='"']])
    
    -- Numbers
    vim.cmd([[syntax match cureNumber "\<\d\+\>"]])
    
    -- Highlighting
    vim.cmd([[highlight link cureKeyword Keyword]])
    vim.cmd([[highlight link cureType Type]])
    vim.cmd([[highlight link cureBuiltin Function]])
    vim.cmd([[highlight link cureComment Comment]])
    vim.cmd([[highlight link cureString String]])
    vim.cmd([[highlight link cureNumber Number]])
  end,
})
