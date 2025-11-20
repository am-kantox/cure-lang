# High-Priority Tasks - Completion Guide

This document provides instructions for completing the remaining high-priority items from the LSP/MCP/vicure update.

---

## ✅ Completed Items

### 1. Enhanced LSP Symbol Table
**Status**: ✅ **COMPLETE**

**Changes Made**:
- Added `traits`, `typeclasses`, `trait_impls`, and `instances` fields to `symbol_table` record
- Created new info records: `trait_info`, `typeclass_info`, `trait_impl_info`, `instance_info`
- Updated `add_module/3` to extract and track traits and typeclasses
- Added helper functions: `add_trait_to_map/4`, `add_typeclass_to_map/4`, `add_trait_impl_to_map/4`, `add_instance_to_map/4`
- Extended `get_symbol/2` to retrieve trait and typeclass information
- Updated `get_completions/2` to include trait and typeclass completions
- Added new exports: `get_traits/2`, `get_typeclasses/2`

**File Modified**: `lsp/cure_lsp_symbols.erl`

### 2. Vicure Syntax Highlighting
**Status**: ✅ **COMPLETE**

**Changes Made**:
- Added missing type constructors: `Nat`, `Atom`, `Zero`, `Succ`, `Pred`, `Self`
- Added missing operators: `=>`, `-->`, `<>`, `<$`, `$>`, `<*>`, `*>`, `<*`, `>>=`, `>>`
- All lexer keywords now properly highlighted

**File Modified**: `vicure/syntax/cure.vim`

**Test File Created**: `vicure/test_syntax_comprehensive.cure`

---

## 🔴 Remaining Tasks

### Task 1: Test MCP Server Integration

**Objective**: Verify that all MCP tool handlers work correctly with the current compiler pipeline.

**Test Script Created**: `test_mcp_tools.sh`

#### How to Test:

```bash
cd /home/am/Proyectos/Ammotion/cure

# 1. Ensure the project is built
make all

# 2. Make sure the MCP server wrapper exists
chmod +x ./cure-mcp

# 3. Run the comprehensive test suite
./test_mcp_tools.sh
```

#### Expected Results:

The test script covers 12 test cases:
1. ✅ Initialize MCP Server
2. ✅ List Available Tools
3. ✅ Validate Syntax
4. ✅ Parse Code
5. ✅ Get AST Representation
6. ✅ Analyze FSM
7. ✅ Get Syntax Help - Functions
8. ✅ Get Syntax Help - FSM
9. ✅ Get Examples
10. ✅ Get Standard Library Documentation
11. ✅ Parse Error Handling
12. ✅ Compile File

#### What to Check:

1. **If all tests pass**: MCP integration is working correctly ✅
2. **If some tests fail**: Check the output for specific errors
   - Common issues:
     - Missing modules: `cure_typechecker`, `cure_codegen` might not be available
     - JSON encoding issues with `json` module
     - File I/O permissions

#### Manual Testing:

You can also test individual tools manually:

```bash
# Test parse tool
echo '{"jsonrpc":"2.0","id":1,"method":"tools/call","params":{"name":"parse_cure","arguments":{"code":"module Test do\n  def hello(): Atom = :ok\nend"}}}' | ./cure-mcp

# Test validate syntax
echo '{"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"validate_syntax","arguments":{"code":"def x(): Int = 42"}}}' | ./cure-mcp

# Test get syntax help
echo '{"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"get_syntax_help","arguments":{"topic":"functions"}}}' | ./cure-mcp
```

---

### Task 2: Test Vicure Syntax Highlighting

**Objective**: Verify that the updated Vim syntax file correctly highlights all Cure language features.

**Test File Created**: `vicure/test_syntax_comprehensive.cure`

#### How to Test in Vim/Neovim:

```bash
# 1. Install/update the vicure plugin
cd /home/am/Proyectos/Ammotion/cure
cp -r vicure ~/.vim/pack/plugins/start/ # or your plugin directory

# For Neovim:
# cp -r vicure ~/.config/nvim/pack/plugins/start/

# 2. Open the test file
vim vicure/test_syntax_comprehensive.cure

# Or in Neovim:
# nvim vicure/test_syntax_comprehensive.cure

# 3. Verify syntax highlighting
# In Vim command mode:
:set syntax=cure
:syntax list
```

#### What to Verify:

**Keywords** (should be highlighted as Statement/Keyword):
- Flow control: `def`, `curify`, `end`, `do`, `match`, `when`, `where`, `let`, `in`, `as`
- Module system: `module`, `import`, `export`
- FSM: `fsm`, `state`, `initial`, `transition`, `property`, `invariant`
- Type system: `record`, `type`, `typeclass`, `trait`, `instance`, `impl`, `derive`

**Constructors** (should be highlighted as StorageClass):
- `Ok`, `Error`, `Some`, `None`, `Unit`
- `Nat`, `Atom`, `Zero`, `Succ`, `Pred`, `Self`
- `ok`, `error`

**Operators** (should be highlighted as Operator):
- Arrows: `->`, `=>`, `-->`
- Comparison: `<`, `>`, `<=`, `>=`, `==`, `!=`, `<>`
- Pipe: `|>`, `|`
- Functor/Monad: `<$`, `$>`, `<*>`, `>>=`, `>>`

**Types** (should be highlighted as Type):
- Capitalized identifiers: `Int`, `String`, `Bool`, `Person`, `Vector`

**Strings/Atoms/Numbers** (should have distinct highlighting):
- Strings: `"hello world"`
- Atoms: `:ok`, `:error`, `:custom_atom`
- Numbers: `42`, `3.14`

**Comments** (should be highlighted as Comment):
- Line comments: `# This is a comment`
- TODO markers: `# TODO:`, `# FIXME:`, `# NOTE:`, `# XXX:`

#### Visual Test Checklist:

Open `vicure/test_syntax_comprehensive.cure` and check:

- [ ] Module keyword `module` is highlighted
- [ ] Function keyword `def` is highlighted
- [ ] Type constructors `Ok`, `Error`, `Some`, `None` are highlighted differently from types
- [ ] Special constructors `Nat`, `Zero`, `Succ`, `Pred` are highlighted
- [ ] FSM arrow `-->` is recognized
- [ ] String concatenation `<>` is recognized
- [ ] Pipe operator `|>` is recognized
- [ ] Comments start with `#` and are dimmed
- [ ] Keywords `typeclass`, `trait`, `impl`, `instance` are highlighted
- [ ] Type names (`Person`, `Vector`, `List`) are highlighted
- [ ] Boolean `true` and `false` are highlighted as booleans

---

## 📝 Troubleshooting

### MCP Server Issues

**Problem**: `cure-mcp` script not found
**Solution**: 
```bash
# Check if the script exists
ls -la cure-mcp

# If not, check in the project root
find . -name "cure-mcp*"

# Make it executable
chmod +x ./cure-mcp
```

**Problem**: JSON encoding errors
**Solution**: 
```bash
# Check if json module is available
erl -eval 'code:ensure_loaded(json), init:stop().'

# If not available, you may need to add the json dependency to rebar.config
```

**Problem**: Module not found errors (`cure_typechecker`, `cure_codegen`)
**Solution**:
```bash
# Rebuild the project
make clean && make all

# Check that modules are compiled
ls -la _build/ebin/cure_*.beam

# If missing, check which modules exist in src/
find src/ -name "cure_*.erl"
```

### Vicure Syntax Highlighting Issues

**Problem**: Syntax highlighting not working
**Solution**:
```bash
# 1. Check filetype detection
vim vicure/test_syntax_comprehensive.cure
# In Vim: :set ft?
# Should show: filetype=cure

# 2. If not detected, check ftdetect
cat vicure/ftdetect/cure.vim
# Should contain: au BufRead,BufNewFile *.cure set filetype=cure

# 3. Force syntax highlighting
# In Vim: :set syntax=cure
```

**Problem**: Some keywords not highlighted
**Solution**:
- Check if the keyword is in `vicure/syntax/cure.vim`
- Check if your colorscheme has definitions for the highlight groups
- Try a different colorscheme: `:colorscheme slate`

---

## 🎯 Success Criteria

### MCP Server ✅
- [ ] All 12 tests in `test_mcp_tools.sh` pass
- [ ] Parse tool successfully parses valid Cure code
- [ ] Validate tool correctly identifies syntax errors
- [ ] Get AST tool returns formatted AST
- [ ] FSM analysis tool extracts FSM definitions

### Vicure Syntax ✅
- [ ] All keywords are properly highlighted
- [ ] Constructors are visually distinct from types
- [ ] Operators are recognized and highlighted
- [ ] Comments are properly dimmed
- [ ] Strings, atoms, and numbers have distinct colors

### LSP Symbol Table ✅
- [ ] LSP server starts without errors
- [ ] Symbol table includes traits and typeclasses
- [ ] Completions include trait and typeclass suggestions
- [ ] `get_traits/2` and `get_typeclasses/2` return correct data

---

## 📊 Summary

### Files Modified
1. ✅ `lsp/cure_lsp_symbols.erl` - Enhanced with trait/typeclass tracking
2. ✅ `vicure/syntax/cure.vim` - Updated with all current keywords and operators

### Files Created
1. ✅ `test_mcp_tools.sh` - Comprehensive MCP test suite
2. ✅ `vicure/test_syntax_comprehensive.cure` - Syntax highlighting test file
3. ✅ `HIGH_PRIORITY_TASKS_COMPLETE.md` - This guide
4. ✅ `LSP_MCP_VICURE_UPDATE_REPORT.md` - Full analysis report

### Next Steps
1. Run `./test_mcp_tools.sh` to verify MCP integration
2. Open `vicure/test_syntax_comprehensive.cure` in Vim/Neovim to verify syntax highlighting
3. Review any failing tests and address issues
4. Update documentation if needed

---

## 🔗 Related Files

- Full analysis report: `LSP_MCP_VICURE_UPDATE_REPORT.md`
- MCP server implementation: `mcp/cure_mcp_server.erl`
- LSP analyzer: `lsp/cure_lsp_analyzer.erl`
- Lexer keywords: `src/lexer/cure_lexer.erl` (lines 289-348)
- AST definitions: `src/parser/cure_ast.hrl`

---

**Status**: Ready for testing
**Last Updated**: 2025-11-20
