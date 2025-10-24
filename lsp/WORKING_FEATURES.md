# Cure LSP - Working Features

This document shows which LSP features currently work and what to expect.

## ✅ Working Features

### 1. **Hover Information** (`K` in NeoVim)

Shows function signature when cursor is anywhere within a function definition.

**Example in `vector_test.cure`:**
- Hover on lines 7-37 (inside `main` function) shows:
  ```cure
  def main() -> Bool
  ```

**Limitations:**
- Only shows info for the containing function, not for called functions yet
- Doesn't show variable types or imported function info
- Function boundaries detected by next `def` keyword (proper Cure syntax)

### 2. **Document Symbols** (`:lua vim.lsp.buf.document_symbol()`)

Lists all symbols in the current file.

**Example output for `vector_test.cure`:**
```
VectorTest (Module)
├── main/0 (Function)
└── len/1 (Function)
```

### 3. **Diagnostics** (Automatic)

Shows syntax errors in real-time.

**Try this:**
1. Add invalid syntax like `thisisnotvalid` in a Cure file
2. Save the file
3. Error should appear with underline and in sign column

### 4. **Go to Definition** (`gd` in NeoVim)

Jump to function definition (currently works same as hover - jumps to containing function).

**Status:** Partially working - needs improvement to find actual definition of called functions

### 5. **Find References** (`gr` in NeoVim)

Find all references to a symbol.

**Status:** Partially working - finds references within same function

## 🚧 Partially Working

### **Completion** (`<C-x><C-o>` in NeoVim)

Basic completion available but not context-aware yet.

**Status:** Returns all symbols but doesn't filter by scope or imports

## ❌ Not Yet Implemented

- **Cross-module references** - Can't jump to imported functions
- **Variable type hover** - Doesn't show types of local variables
- **Semantic highlighting** - No syntax highlighting from LSP yet
- **Code actions** - No quick fixes or refactorings
- **Rename** - Symbol renaming not implemented
- **Formatting** - No auto-formatting yet

## Testing in NeoVim

### Prerequisites
```bash
cd /opt/Proyectos/Ammotion/cure
make clean && make lsp
./cure-lsp --version
```

### Open a file
```bash
nvim examples/vector_test.cure
```

### Test hover
1. Move cursor to line 8 (inside `main` function)
2. Press `K`
3. Should see floating window with:
   ```
   ```cure
   def main() -> Bool
   ``` 
   ```

### Test document symbols
```vim
:lua vim.lsp.buf.document_symbol()
```
Should open a list with module and function names.

### Test diagnostics
1. Add a syntax error: `module Test do thisisbroken end`
2. Save (`:w`)
3. Should see error diagnostics appear

## Expected Behavior

### ✓ Success Cases

| Action | Expected Result |
|--------|----------------|
| Open `.cure` file | LSP attaches, see "✓ Cure LSP attached" message |
| `:LspInfo` | Shows `cure_lsp` client attached |
| Hover on function body | Shows function signature in floating window |
| `:lua vim.lsp.buf.document_symbol()` | Lists all symbols |
| Invalid syntax + save | Shows diagnostics with error |

### ✗ Known Limitations

| Action | Current Behavior | Desired Behavior |
|--------|------------------|------------------|
| Hover on function call | Shows containing function | Should show called function signature |
| Hover on variable | Shows containing function | Should show variable type |
| Hover on imported function | Shows nothing | Should show function from imported module |
| Completion | Shows all symbols | Should filter by context and imports |

## Debug Commands

If something doesn't work:

```vim
" Check LSP is attached
:LspInfo

" View LSP logs
:LspLog

" Restart LSP
:LspRestart

" Stop LSP
:LspStop

" Start LSP manually
:LspStart cure_lsp
```

## What's Next?

To improve these features, we need to implement:

1. **Better position-to-symbol resolution**
   - Parse AST to find exact identifier at cursor
   - Use cure_lsp_document module to extract word at position
   
2. **Workspace symbol indexing**
   - Index all modules in workspace
   - Resolve cross-module references
   
3. **Type inference integration**
   - Connect to cure_typechecker
   - Show inferred types on hover
   
4. **Context-aware completion**
   - Filter by scope
   - Show only imported symbols
   - Add snippets for common patterns

## Current Limitations Explained

### Why hover only shows containing function?

The current implementation uses `find_symbol_at_position` which checks if the cursor is within a function's boundaries (from `def` keyword to the next `def` or end of module). It correctly handles Cure's syntax where functions don't have explicit `end` keywords. However, it doesn't yet parse the function body to find specific identifiers under the cursor.

**To fix:** Need to traverse the AST and find the exact AST node (identifier, function call, etc.) at the cursor position.

### Why can't I jump to imported functions?

The LSP currently only indexes the current file. It doesn't load or parse imported modules.

**To fix:** Need workspace indexing that parses all `.cure` files and builds a global symbol table.

### Why is completion not filtered?

The completion handler returns all symbols from the symbol table without filtering by scope or visibility.

**To fix:** Need to:
1. Determine cursor context (inside what scope?)
2. Filter symbols by visibility rules
3. Prioritize recently used and contextually relevant symbols

## Report Issues

When reporting issues, please include:
1. Output of `:LspInfo`
2. Relevant lines from `:LspLog`
3. The Cure code you're testing with
4. What you expected vs what happened
