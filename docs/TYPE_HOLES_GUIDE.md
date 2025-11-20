# Type Holes - Interactive Type Inference

## Overview

Type holes provide an interactive way to discover types in Cure, inspired by Idris and Agda. Instead of manually writing type annotations, you can use **holes** and let the SMT-based type checker infer the correct type for you.

## Syntax

### Anonymous Hole: `_`
```cure
def double_list(numbers: List(Int)): _ =
    map(numbers, fn(x) -> x * 2 end)
```

### Named Hole: `?name`
```cure
def process(x: ?input_type): Int =
    x + 1
```

## Usage Workflow

### 1. Write code with holes
```cure
def double_list(numbers: List(Int)): _ =
    map(numbers, fn(x) -> x * 2 end)
```

### 2. Hover to see inferred type
When you hover over the `_`, the LSP shows:
```
Type hole: _
Inferred type: List(Int)
```

### 3. Apply quick fix
The LSP provides a code action: **"Fill hole with: List(Int)"**

Click it, and the code becomes:
```cure
def double_list(numbers: List(Int)): List(Int) =
    map(numbers, fn(x) -> x * 2 end)
```

## Where You Can Use Holes

### Function Return Types
```cure
def calculate(): _ =
    42  % Infers: Int
```

### Parameter Types
```cure
def add(x: _, y: _): Int =
    x + y  % Infers: x :: Int, y :: Int
```

### Let Bindings
```cure
let result: _ = some_function()
% Shows inferred type from some_function's return type
```

### Complex Types
```cure
def process_list(xs: _): _ =
    map(xs, fn(x) -> x * 2 end)
% Infers: xs :: List(Int), return :: List(Int)
```

## LSP Features

### Diagnostics
Type holes appear as **information-level** diagnostics (blue underline in most editors):
- **Severity**: Info (not an error)
- **Message**: "Type hole: _ \n Inferred type: List(Int)"
- **Source**: `cure-holes`

### Hover
Hovering shows:
```markdown
**Type Hole: `_`**

Inferred type: `List(Int)`

Use code action to fill in this type.
```

### Code Actions
When your cursor is on a hole, you get a quick fix:
- **Title**: "Fill hole with: List(Int)"
- **Kind**: quickfix
- **Action**: Replaces the hole with the inferred type

## Editor Setup

### Neovim with nvim-lspconfig

```lua
require('lspconfig').cure_ls.setup{
  capabilities = capabilities,
  settings = {
    cure = {
      typeHoles = {
        enabled = true,
        showDiagnostics = true  -- Show info-level diagnostics for holes
      }
    }
  }
}
```

**Keybindings**:
```lua
vim.keymap.set('n', 'K', vim.lsp.buf.hover)  -- Show hover on 'K'
vim.keymap.set('n', '<leader>ca', vim.lsp.buf.code_action)  -- Code action
```

### VSCode

The Cure extension automatically enables type holes. To apply a code action:
1. Place cursor on the hole
2. Press `Ctrl+.` (or `Cmd+.` on Mac)
3. Select "Fill hole with: ..."

### Emacs with lsp-mode

```elisp
(use-package lsp-mode
  :custom
  (lsp-cure-type-holes-enabled t))
```

## Advanced Usage

### Named Holes for Documentation

Use named holes to document what type you're looking for:

```cure
def complex_computation(input: List(?element_type)): ?result =
    % ... complex logic ...
    result
```

The LSP will show:
- Hover on `?element_type`: "Type hole: ?element_type → Inferred: Int"
- Hover on `?result`: "Type hole: ?result → Inferred: List(Int)"

### Progressive Type Refinement

Start with holes and progressively fill them in as you understand the code:

```cure
% Step 1: All holes
def mystery(x: _): _ = x * 2

% Step 2: Fill in return type after hovering
def mystery(x: _): Int = x * 2

% Step 3: Fill in parameter type
def mystery(x: Int): Int = x * 2
```

### Type Holes with SMT Constraints

For dependent types, holes can help discover refinement constraints:

```cure
def safe_divide(a: Int, b: _): Int =
    a / b
    
% Hover shows: b :: Int when b /= 0
% (if SMT solver detects the constraint)
```

## How It Works

### Type Inference Algorithm

1. **AST Analysis**: Parser marks `_` and `?name` as type holes
2. **Context Collection**: LSP collects surrounding type information
3. **Type Checking**: Runs standard type checker on the AST
4. **Constraint Solving**: Uses SMT solver for dependent type constraints
5. **Type Extraction**: Extracts inferred type from type checker result

### SMT Integration

For dependent types with refinement constraints:

```cure
def process(n: _): Positive =
    n + 1
    
% SMT solver infers: n :: Int when n > -1
% (because n + 1 must be > 0)
```

The SMT solver works backwards from constraints to infer the tightest possible type.

## Limitations

### Cannot Infer

1. **Polymorphic types without context**:
   ```cure
   def identity(x: _): _ = x  % Too generic, need more context
   ```

2. **Recursive types without annotation**:
   ```cure
   def recursive(n: _): _ =
       if n == 0 then 1 else n * recursive(n - 1)
   % Needs explicit type to establish recursion
   ```

3. **Higher-rank polymorphism**:
   ```cure
   def apply(f: _): _ = f(42)  % f's type is higher-rank
   ```

### Workarounds

For cases where inference fails:
1. **Add partial annotations**: Fill in parameter types, leave return type as hole
2. **Use named holes**: Helps you track what needs to be filled
3. **Check hover message**: It will tell you why inference failed

## Examples

### Example 1: List Processing

```cure
module Examples do
  import Std.List [map, filter, fold]
  
  % Before: with holes
  def process_numbers(nums: _): _ =
      let doubled: _ = map(nums, fn(x) -> x * 2 end)
      let evens: _ = filter(doubled, fn(x) -> x % 2 == 0 end)
      fold(evens, 0, fn(acc, x) -> acc + x end)
  
  % After: hovering and applying quick fixes
  def process_numbers(nums: List(Int)): Int =
      let doubled: List(Int) = map(nums, fn(x) -> x * 2 end)
      let evens: List(Int) = filter(doubled, fn(x) -> x % 2 == 0 end)
      fold(evens, 0, fn(acc, x) -> acc + x end)
end
```

### Example 2: Dependent Types

```cure
% Use hole for refinement type
type Positive = Int when x > 0

def divide(a: Int, b: _): Int =
    a / b
    
% Hover on b shows: "Inferred: Positive"
% Because SMT proves division is safe only when b > 0
```

### Example 3: Pattern Matching

```cure
def describe(opt: _): _ =
    match opt do
        | Some(n) -> "Value: " <> to_string(n)
        | None -> "No value"
    end
    
% Infers: opt :: Option(Int), return :: String
```

## Troubleshooting

### "Cannot infer type" message

**Cause**: Not enough context for inference

**Solutions**:
1. Add more type annotations to surrounding code
2. Fill in parameter types, use hole for return type only
3. Check if you're using polymorphic code without constraints

### Hole not detected

**Cause**: Syntax not recognized as hole

**Solutions**:
1. Use `_` not `__` (double underscore)
2. Ensure `?name` starts with `?` character
3. Restart LSP server: `:LspRestart` in Neovim

### Wrong type inferred

**Cause**: Inference algorithm limitation or bug

**Solutions**:
1. Check surrounding code for type errors
2. Add explicit type annotation instead
3. Report as bug with minimal reproduction

## Best Practices

1. **Start broad**: Use holes for all types initially
2. **Refine incrementally**: Fill in types from bottom-up (parameters → return)
3. **Document intent**: Use named holes like `?result_type` for clarity
4. **Verify inference**: Always check the inferred type makes sense
5. **Keep holes during development**: Remove once code is stable

## Comparison with Other Languages

### Idris
```idris
-- Idris uses ?hole syntax
f : ?hole
f x = x + 1

-- Cure equivalent:
def f(x: _): _ = x + 1
```

### Agda
```agda
-- Agda uses {! !} or ?
f : ?
f x = x + 1

-- Cure equivalent:
def f(x: _): _ = x + 1
```

### Haskell (with Typed Holes)
```haskell
f :: _
f x = x + 1

-- Direct equivalent in Cure:
def f(x: _): _ = x + 1
```

## Future Enhancements

Planned features for type holes:

1. **Multiple choice inference**: Show several possible types
2. **Constraint suggestions**: "Consider adding: when x > 0"
3. **Interactive refinement**: Incrementally refine polymorphic types
4. **Case splitting**: Generate pattern match cases for sum types
5. **Proof obligations**: Show what needs to be proven for dependent types

---

**Happy type hunting! 🎯**

For issues: https://github.com/cure-lang/cure/issues
