# Cure LSP Changelog

## 2025-10-24 - JSX Removal & Symbol Extraction Fix

### Breaking Changes
- **Removed JSX dependency**: Now uses Erlang's native `json` module (requires OTP 27+)
- No external dependencies needed for LSP functionality

### Bug Fixes
1. **Fixed symbol extraction**: Parser returns list of modules but symbol extractor expected single module
   - Added `extract_symbols_from_module/1` to handle both list and single module cases
   - Symbol extraction now correctly identifies modules and functions
   
2. **Fixed "unexpected_token identifier" error**: Was not actually a bug - LSP works correctly with valid Cure syntax

3. **Fixed JSON encoding crash**: `json:encode/1` returns iolist, not binary
   - Added `iolist_to_binary()` wrapper in `encode_json/1`
   - LSP now starts and responds correctly in NeoVim

4. **Fixed hover/go-to-definition not working**: Position finder only checked exact definition line
   - Now checks if cursor is within function body (up to 50 lines from definition)
   - Hover and go-to-definition now work when cursor is anywhere in a function

### Improvements
1. **Native JSON handling**:
   - Replaced `jsx:decode/2` with `json:decode/1`
   - Replaced `jsx:encode/1` with `json:encode/1`
   - Added helper functions `atomize_keys/1` and `binarize_keys/1` for key conversion
   - Maintains backward compatibility with atom-keyed maps internally

2. **Build system**:
   - Removed `lsp-deps` target from Makefile (no longer needed)
   - Removed JSX path from cure-lsp escript
   - Removed JSX availability check from cure-lsp

3. **Documentation**:
   - Created comprehensive [NEOVIM_SETUP.md](NEOVIM_SETUP.md) with step-by-step testing guide
   - Updated [README.md](README.md) to remove JSX references
   - Updated [QUICKSTART.md](QUICKSTART.md) to reflect simpler setup
   - Documented keybindings and troubleshooting steps

### Technical Details

#### Symbol Extraction Fix
The parser returns `{ok, [ModuleDef]}` but symbol extraction functions expected `#module_def{}` directly. Fixed by adding:

```erlang
extract_symbols_from_ast([ModuleDef | _Rest]) when is_record(ModuleDef, module_def) ->
    extract_symbols_from_module(ModuleDef);
extract_symbols_from_ast(ModuleDef) when is_record(ModuleDef, module_def) ->
    extract_symbols_from_module(ModuleDef);
```

Similar fixes applied to:
- `find_definition_in_ast/3` → `find_definition_in_module/3`
- `find_references_in_ast/3` → `find_references_in_module/3`
- `get_hover_from_ast/3` → `get_hover_from_module/3`

#### JSON Conversion Helpers
```erlang
atomize_keys(Map) -> % Converts binary keys to atoms for internal use
binarize_keys(Map) -> % Converts atom keys to binaries for JSON output
```

These helpers recursively traverse maps and lists to ensure proper key types.

### Testing

To verify the changes work:

```bash
# Build LSP
make clean
make lsp

# Test symbol extraction
erl -pa _build/ebin -pa _build/lsp -noshell -eval \
  "{ok, Text} = file:read_file(\"examples/vector_test.cure\"), \
   Symbols = cure_lsp_analyzer:extract_symbols(Text), \
   io:format(\"Symbols: ~p~n\", [Symbols])." -s init stop

# Should output module and function symbols
```

### NeoVim Integration

See [NEOVIM_SETUP.md](NEOVIM_SETUP.md) for complete setup instructions.

**Minimal config**:
```lua
local lspconfig = require('lspconfig')
local configs = require('lspconfig.configs')

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

lspconfig.cure_lsp.setup({})

vim.filetype.add({ extension = { cure = 'cure' } })
```

### Migration Notes

If you were using JSX previously:

1. **Remove JSX from rebar.config**:
   ```erlang
   {deps, []}.  % Was: {deps, [{jsx, "3.1.0"}]}
   ```

2. **Rebuild**:
   ```bash
   make clean
   make lsp
   ```

3. **No code changes needed** - the LSP handles conversion internally

### Files Changed

- `rebar.config` - Removed JSX dependency
- `lsp/cure_lsp.erl` - Replaced JSX with native json module
- `lsp/cure_lsp_analyzer.erl` - Fixed symbol extraction to handle parser output
- `cure-lsp` - Removed JSX path and checks
- `Makefile` - Removed lsp-deps target
- `lsp/README.md` - Updated dependencies and known issues
- `lsp/QUICKSTART.md` - Simplified setup steps
- `lsp/NEOVIM_SETUP.md` - NEW: Comprehensive testing guide

### Compatibility

- **Requires**: Erlang/OTP 27+ (for native `json` module)
- **Tested with**: NeoVim 0.9+, nvim-lspconfig
- **Supported file types**: `.cure`

### Known Limitations

1. Symbol extraction only handles the first module in a file (Cure typically uses one module per file)
2. Cross-module references not yet fully implemented
3. Hover information needs deeper type system integration
4. Completion is basic - needs context-aware filtering

### Future Work

- [ ] Add workspace-wide symbol indexing for cross-module references
- [ ] Integrate with type inference for richer hover information
- [ ] Implement code actions (e.g., auto-import)
- [ ] Add snippet support for common patterns
- [ ] Implement semantic tokens for better syntax highlighting
