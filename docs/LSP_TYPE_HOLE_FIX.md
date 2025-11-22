# LSP Type Hole Code Action Fix

## Problem

When using a type hole (`_`) in a Cure source file, such as:

```cure
def create_person(): _ =
  Person{name: "Alice", age: 30, email: "alice@example.com"}
```

The LSP server was not providing code actions to fill in the inferred type, even though the type inference system was working correctly.

## Root Cause

The `cure_lsp_type_holes` module existed in `/lsp/cure_lsp_type_holes.erl` but was not present in the `/src/lsp/` directory where the LSP server expected to find it. The LSP server (`src/lsp/cure_lsp_server.erl`) was attempting to call `cure_lsp_type_holes:generate_hole_diagnostics/2` and `cure_lsp_type_holes:generate_hole_code_actions/3`, but these modules weren't being compiled into the build.

## Solution

Copied the type holes module from its original location to where the compiler expects it:

```bash
cp lsp/cure_lsp_type_holes.erl src/lsp/cure_lsp_type_holes.erl
```

The module is now properly compiled during the build process and available to the LSP server.

## How It Works

### Type Hole Detection

The LSP server now properly detects type holes in three locations:

1. **Return type holes**: `def func(): _ = ...`
2. **Parameter type holes**: `def func(x: _): Int = ...`
3. **Named holes**: `def func(): ?returnType = ...`

### Diagnostics

When a type hole is detected, the LSP generates an information-level diagnostic showing:
- The hole name
- The inferred type
- A hint to use the Quick Fix action (Ctrl+.)

Example diagnostic message:
```
Type hole: _
Inferred type: Person

💡 Click 'Quick Fix' or press Ctrl+. to fill in the type automatically
```

### Code Actions

The LSP provides a "quickfix" code action titled `"Fill hole with: Person"` that:
1. Replaces the `_` character with the inferred type name
2. Is marked as "preferred" for automatic application
3. Works with the diagnostic range to precisely target the underscore

## Implementation Details

### Module Structure

The `cure_lsp_type_holes` module provides:

- `find_type_holes/1` - Detects all type holes in an AST
- `is_type_hole/1` - Checks if a type expression is a hole
- `infer_hole_type/3` - Infers the type for a hole using the type checker
- `generate_hole_diagnostics/2` - Creates LSP diagnostics for holes
- `generate_hole_code_actions/3` - Creates code actions to fill holes
- `generate_hole_hover/3` - Provides hover information for holes

### Type Inference

The module uses the full Cure type checker to infer types:

1. Builds a type environment including imports from the module
2. Calls `cure_typechecker:check_function/2` with the function definition
3. Extracts the return type from the type checker result
4. Converts internal type representation to AST format for display

### Integration Points

The LSP server integrates type holes at two key points:

1. **Document Analysis** (line 473 of `cure_lsp_server.erl`):
   ```erlang
   HoleDiagnostics = run_type_holes(Uri, AST)
   ```

2. **Code Actions** (line 306 of `cure_lsp_server.erl`):
   ```erlang
   HoleActions = cure_lsp_type_holes:generate_hole_code_actions(Uri, Diagnostic, AST)
   ```

## Testing

To verify the fix works:

1. Open `examples/15_records_comprehensive.cure` in your editor
2. Change line 35 from `def create_person(): Person =` to `def create_person(): _ =`
3. You should see an information diagnostic appear on the type hole
4. Trigger code actions (Ctrl+. or right-click -> Quick Fix)
5. Select "Fill hole with: Person"
6. The `_` should be replaced with `Person`

## Related Files

- `/src/lsp/cure_lsp_type_holes.erl` - Type hole detection and inference
- `/src/lsp/cure_lsp_server.erl` - LSP server main logic
- `/src/types/cure_typechecker.erl` - Type inference engine
- `/examples/15_records_comprehensive.cure` - Example demonstrating records

## Date

2025-11-21
