# Type Holes - Quick Start Guide

## What Are Type Holes?

Type holes let you write `_` where a type is expected, and the LSP will automatically **infer and substitute** the correct type for you.

## How It Works

### 1. Write Code with `_` as Placeholder

```cure
def double_list(numbers: List(Int)): _ =
    map(numbers, fn(x) -> x * 2 end)
```

### 2. LSP Shows Diagnostic

When you save or the LSP analyzes the file, you'll see:

```
💡 Type hole: _
Inferred type: List(Int)

💡 Click 'Quick Fix' or press Ctrl+. to fill in the type automatically
```

### 3. Apply Quick Fix

**Option A: Keyboard**
- Place cursor on the `_`
- Press `Ctrl+.` (or `Cmd+.` on Mac)
- Select "Fill hole with: List(Int)"

**Option B: Mouse**
- Click on the diagnostic (lightbulb icon)
- Click "Fill hole with: List(Int)"

**Option C: Auto-apply (if supported)**
- Some editors auto-apply the "preferred" quick fix
- Just save the file and the type fills in automatically

### 4. Result

```cure
def double_list(numbers: List(Int)): List(Int) =
    map(numbers, fn(x) -> x * 2 end)
```

The `_` is **automatically replaced** with `List(Int)`!

## Editor-Specific Instructions

### Neovim with nvim-lspconfig

```lua
-- In your config
vim.keymap.set('n', '<leader>ca', vim.lsp.buf.code_action, { desc = 'Code Action' })
```

**Usage:**
1. Place cursor on `_`
2. Press `<leader>ca` (usually Space+c+a)
3. Select the code action from the menu

**Or use auto-fix:**
```lua
-- Automatically apply preferred quick fixes
vim.keymap.set('n', '<leader>qf', function()
  vim.lsp.buf.code_action({
    filter = function(action)
      return action.isPreferred
    end,
    apply = true
  })
end, { desc = 'Quick Fix' })
```

### VS Code

**Automatic:**
- Just type `_` and save
- VS Code may auto-suggest the type
- Accept with `Tab` or `Enter`

**Manual:**
- Click the lightbulb 💡 icon
- Or press `Ctrl+.`
- Select "Fill hole with: ..."

### Emacs with lsp-mode

```elisp
(define-key lsp-mode-map (kbd "C-c C-a") 'lsp-execute-code-action)
```

**Usage:**
1. Move point to `_`
2. Press `C-c C-a`
3. Select the fill action

## Examples

### Example 1: Function Return Type

```cure
# Before
def process(nums: List(Int)): _ =
    filter(nums, fn(x) -> x > 0 end)

# After quick fix
def process(nums: List(Int)): List(Int) =
    filter(nums, fn(x) -> x > 0 end)
```

### Example 2: Parameter Types

```cure
# Before  
def add(x: _, y: _): Int =
    x + y

# After quick fix (both holes filled)
def add(x: Int, y: Int): Int =
    x + y
```

### Example 3: Complex Types

```cure
# Before
def nested_map(lists: _): _ =
    map(lists, fn(xs) -> map(xs, fn(x) -> x * 2 end) end)

# After quick fix
def nested_map(lists: List(List(Int))): List(List(Int)) =
    map(lists, fn(xs) -> map(xs, fn(x) -> x * 2 end) end)
```

## Workflow Tips

### Incremental Type Filling

Start with all `_`, then fill types one by one:

```cure
# Step 1: All holes
def complex(a: _, b: _): _ = 
    some_function(a, b)

# Step 2: Fill parameters (from hover or quick fix)
def complex(a: Int, b: String): _ = 
    some_function(a, b)

# Step 3: Fill return type
def complex(a: Int, b: String): Result(String) = 
    some_function(a, b)
```

### Use Hover for Preview

Before applying the quick fix:
1. Hover over `_` to see inferred type
2. Check if it looks correct
3. Apply quick fix if satisfied

## Troubleshooting

### "Cannot infer type"

**Problem:** LSP can't determine the type

**Solutions:**
1. Fill in parameter types first
2. Add more context (type annotations nearby)
3. Check if the expression is too ambiguous
4. Manually provide the type

### Quick fix not appearing

**Problem:** No code action shows up

**Checklist:**
- [ ] Is the `_` actually a type hole (not in an expression)?
- [ ] Did the LSP server analyze the file? (save/reload)
- [ ] Check LSP logs: `:LspLog` (Neovim) or View → Output → Language Server (VS Code)
- [ ] Restart LSP: `:LspRestart` (Neovim) or Reload Window (VS Code)

### Wrong type inferred

**Problem:** LSP suggests incorrect type

**Solutions:**
1. Provide more context nearby
2. Add explicit annotations on parameters
3. Manually fill the type
4. Report as a bug with minimal reproduction

## Advanced: Batch Fill

Some editors support batch operations:

```cure
# Multiple holes in one file
def f1(x: _): _ = x + 1
def f2(y: _): _ = y * 2  
def f3(z: _): _ = z / 3
```

**VS Code:**
- Source Action → Fill all type holes

**Neovim:**
```lua
-- Custom command to fill all holes in buffer
vim.api.nvim_create_user_command('FillAllHoles', function()
  vim.lsp.buf.code_action({
    context = { only = {'quickfix'} },
    filter = function(action)
      return string.match(action.title, '^Fill hole')
    end,
    apply = true
  })
end, {})
```

## Benefits

✅ **Faster development** - Less typing  
✅ **Fewer typos** - LSP ensures correctness  
✅ **Learn types** - See what types are inferred  
✅ **Refactoring** - Change implementation, let LSP update types  
✅ **Exploration** - Try code, see what type emerges  

## Next Steps

- Read full guide: `docs/TYPE_HOLES_GUIDE.md`
- Try examples: `examples/type_holes_demo.cure`
- Configure editor: See guide for your specific editor

---

**Happy type-free coding! 🎯**
