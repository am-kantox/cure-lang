# Typeclass Export Feature

## Overview

The `export_typeclasses` feature provides a proper mechanism for exporting typeclasses and their instances from Cure modules. This addresses the semantic mismatch between how typeclasses work (polymorphic methods across instances) and how the traditional export system works (concrete function definitions).

## Motivation

Previously, attempting to export typeclass methods like `show/1` would fail because:
1. Typeclass methods are defined inside `instance` definitions, not as top-level functions
2. The export validator only looked for top-level `function_def` or `curify_function_def` records
3. There was no way to indicate that a typeclass (with all its instances) should be exported

## Syntax

### Basic Usage

```cure
module Std.Show do
  export_typeclasses [Show]
  export [show_list/1, show_separated/2]
  
  typeclass Show(T) do
    def show(x: T): String
  end
  
  instance Show(Int) do
    def show(x: Int): String = "<int>"
  end
  
  # ... more instances
end
```

### Multiple Typeclasses

```cure
module Std.Comparison do
  export_typeclasses [Eq, Ord]
  export [compare/2, min/2, max/2]
  
  typeclass Eq(T) do
    def equals(x: T, y: T): Bool
  end
  
  typeclass Ord(T) do
    def compare(x: T, y: T): Ordering
  end
  
  # ... instances
end
```

## Implementation Details

### Changes Made

1. **Lexer** (`cure_lexer.erl`):
   - Added `export_typeclasses` as a new keyword token

2. **AST** (`cure_ast.hrl`):
   - Added `#typeclass_export_list{}` record with fields:
     - `typeclasses`: List of typeclass names (atoms)
     - `location`: Source location

3. **Parser** (`cure_parser.erl`):
   - Added `parse_export_typeclasses/1` function
   - Added `parse_typeclass_names/2` helper
   - Updated `collect_exports_helper/4` to handle typeclass exports
   - Added handling in `parse_module_item/1`

4. **Type Checker** (`cure_typechecker.erl`):
   - Updated `extract_export_specs/2` to recognize typeclass exports
   - Updated `check_exports/2` with new clause for `#typeclass_export_list{}`
   - Added `validate_typeclass_exports/3` to verify exported typeclasses exist
   - Added `find_typeclass/2` helper function

### Validation

When a module uses `export_typeclasses [Name1, Name2, ...]`, the type checker:
1. Verifies each typeclass is defined in the module
2. Returns an error if a referenced typeclass doesn't exist
3. Allows the module to compile if all typeclasses are present

## Semantics

### What Gets Exported

When you export a typeclass:
- The typeclass definition itself is exported
- All instances defined in the same module are exported
- The typeclass methods become available for use (through typeclass resolution)

### Import Semantics

When another module imports from a module that exports typeclasses:
```cure
import Std.Show [Show]  # Imports the Show typeclass and all its instances
```

The typeclass and all its instances become available in the importing module.

## Benefits

1. **Semantic Correctness**: Typeclasses are exported as typeclasses, not as individual methods
2. **Clean Separation**: Regular function exports (`export [...]`) vs. typeclass exports (`export_typeclasses [...]`)
3. **Better Error Messages**: Specific error for missing typeclasses vs. missing functions
4. **Extensibility**: Easy to add more typeclass-specific validation in the future

## Migration Guide

### Before

```cure
module Std.Show do
  export [show/1, show_list/1, show_separated/2]  # ❌ Fails: show/1 not found
  
  typeclass Show(T) do
    def show(x: T): String
  end
  
  instance Show(Int) do
    def show(x: Int): String = "<int>"
  end
end
```

### After

```cure
module Std.Show do
  export_typeclasses [Show]                       # ✅ Exports the typeclass
  export [show_list/1, show_separated/2]          # ✅ Exports helper functions
  
  typeclass Show(T) do
    def show(x: T): String
  end
  
  instance Show(Int) do
    def show(x: Int): String = "<int>"
  end
end
```

## Examples

See:
- `lib/std/show.cure` - Real-world usage in standard library
- `examples/typeclass_export_demo.cure` - Simple demonstration

## Future Enhancements

Potential future improvements:
1. Allow selective instance exports: `export_typeclasses [Show(Int, String)]`
2. Support re-exporting typeclasses from imported modules
3. Add typeclass visibility modifiers (public/private instances)
4. Generate documentation showing which instances are exported
