# Cure LSP Quick Reference

## What Gets Checked

The Cure LSP performs three layers of analysis on every save/change:

### 1. Syntax Analysis
- **Lexer**: Tokenization errors (invalid characters, malformed strings)
- **Parser**: Syntax errors (missing keywords, unbalanced brackets)

### 2. Type Checking
- **Type mismatches**: Operations on incompatible types
- **Undefined variables**: References to unbound identifiers
- **Function signatures**: Parameter and return type matching
- **Generic constraints**: Type parameter satisfaction
- **FSM handlers**: Event handler signature validation

### 3. SMT Verification
- **Pattern exhaustiveness**: All match cases covered
- **Refinement types**: Type predicates satisfied (e.g., `n > 0`)
- **Dependent constraints**: Type-level constraints proven

## Error Severity

| Severity | Color | Meaning | Example |
|----------|-------|---------|---------|
| **Error** | 🔴 Red | Prevents compilation | Type mismatch, undefined variable |
| **Warning** | 🟡 Yellow | Potential issue | Non-exhaustive pattern, unused variable |
| **Info** | 🔵 Blue | Suggestion | Consider adding type annotation |
| **Hint** | ⚪ Gray | Style | Naming convention, simplification |

## Common Diagnostics

### Type Errors

#### Type Mismatch
```cure
def add(x: Int, y: String) -> Int do
    x + y  // Error: Cannot add Int and String
end
```
**Fix**: Ensure operands have compatible types.

#### Undefined Variable
```cure
def foo() -> Int do
    x + 1  // Error: Variable 'x' undefined
end
```
**Fix**: Define the variable or add it as a parameter.

#### Generic Constraint Violation
```cure
def sum<T: Numeric>(a: T, b: T) -> T do
    a + b
end

sum("hello", "world")  // Error: String doesn't satisfy Numeric
```
**Fix**: Use a type that satisfies the constraint.

### SMT Warnings

#### Non-exhaustive Pattern Match
```cure
def describe(opt: Option(Int)) -> String do
    match opt do
        | Some(n) -> "Has value"
        // Warning: Missing case for None
    end
end
```
**Fix**: Add the missing pattern:
```cure
def describe(opt: Option(Int)) -> String do
    match opt do
        | Some(n) -> "Has value"
        | None -> "No value"
    end
end
```

#### Refinement Type Violation
```cure
type PositiveInt = Int when n > 0

def divide(x: Int, y: PositiveInt) -> Int do
    x / y
end

divide(10, -5)  // Error: Refinement violated, -5 is not > 0
```
**Fix**: Pass a value that satisfies the refinement.

## LSP Commands

### In Neovim

| Key | Command | Description |
|-----|---------|-------------|
| `K` | Hover | Show type information |
| `gd` | Go to definition | Jump to symbol definition |
| `gr` | Find references | Show all references |
| `<space>e` | Open diagnostic | Show error details |
| `[d` | Previous diagnostic | Jump to previous error |
| `]d` | Next diagnostic | Jump to next error |

### Programmatic

```erlang
% Check a document
cure_lsp_server:update_document(Uri, Content).

% Get diagnostics
Diagnostics = cure_lsp_server:get_diagnostics(Uri).

% Run type checker manually
Errors = cure_typechecker:check_module(AST, Env).

% Run SMT verification
SmtErrors = cure_lsp_smt:verify_refinement_types(AST).
```

## Configuration

### Neovim init.lua

```lua
lspconfig.cure_lsp.setup({
  settings = {
    cure = {
      -- Enable/disable features
      typeChecking = true,
      smtVerification = true,
      patternExhaustiveness = true,
      
      -- SMT solver selection
      smtSolver = "z3",  -- "z3", "cvc5", or "symbolic"
      
      -- Timeouts (milliseconds)
      typecheckTimeout = 5000,
      smtTimeout = 5000,
    }
  }
})
```

## Performance Tips

### For Large Files

If analysis is slow:
1. Disable SMT verification temporarily
2. Increase timeouts
3. Use symbolic evaluation instead of Z3

```lua
settings = {
  cure = {
    smtVerification = false,  -- Disable for large files
  }
}
```

### For Projects with Many Modules

- LSP caches type environments per module
- Only changed files are re-analyzed
- Cross-module resolution is incremental

## Troubleshooting

### No Diagnostics Shown

**Check**:
1. LSP server is running: `:LspInfo` in Neovim
2. File is recognized as Cure: `:set filetype?` should show `cure`
3. No parser errors blocking type checking

**Debug**:
```vim
:LspLog  " View LSP logs
:LspRestart cure_lsp  " Restart the server
```

### False Positives

If the LSP reports errors for valid code:

1. Check if you're using latest LSP version
2. Verify type annotations are correct
3. Try adding explicit type annotations to help inference

**Report bugs** with minimal reproduction:
```cure
% Minimal example that triggers false positive
def buggy_function() -> Int do
    42
end
```

### Slow Analysis

If the LSP feels sluggish:

1. Check file size (>1000 lines may be slow)
2. Disable SMT verification
3. Reduce timeouts
4. Check Z3/CVC5 installation

**Profile**:
```erlang
% In Erlang shell
timer:tc(fun() -> cure_typechecker:check_module(AST, Env) end).
```

## Advanced Features

### Type Inference Hints

The LSP can suggest inferred types:

```cure
def mystery_function(x) do  // Hint: x: Int
    x + 1
end
```

Enable in settings:
```lua
settings = {
  cure = {
    inlayHints = true
  }
}
```

### Code Actions

Future feature: Quick fixes for common errors

- Add missing pattern case
- Add type annotation
- Import missing module
- Fix type mismatch by conversion

## Resources

- [Full LSP Documentation](./README.md)
- [SMT Integration Details](./LSP_SMT_INTEGRATION.md)
- [Type System Reference](../docs/TYPE_SYSTEM.md)
- [SMT Solver Guide](../docs/SMT_QUICK_REFERENCE.md)
