# Typeclass Import System Implementation

## Overview

The Cure type checker now supports importing typeclasses and their instances from other modules. This enables modular typeclass-based programming where typeclasses can be defined in library modules and imported by user code.

## Implementation Date

November 24, 2024

## Problem Statement

Previously, when a module attempted to use a typeclass method (e.g., `show(42)`), the type checker would report an unbound variable error even if the module imported from a typeclass-defining module. This was because the import system only handled function imports, not typeclass definitions or instances.

## Solution

Enhanced the import system in `cure_typechecker.erl` to automatically load and register typeclasses and instances from imported modules.

## Key Changes

### 1. Enhanced `check_import_items` Function (Line 3316)

```erlang
check_import_items(Module, Items, Env) ->
    % First, load typeclasses and instances from the imported module
    EnvWithTypeclasses = import_module_typeclasses(Module, Env),
    % Then, import the requested items (functions, types, etc.)
    import_items(Module, Items, EnvWithTypeclasses).
```

### 2. New `import_module_typeclasses` Function (Line 3333)

This function:
1. Converts the module name to a file path (e.g., `'Std.Show'` → `"lib/std/show.cure"`)
2. Parses the imported module's AST
3. Extracts typeclass definitions and instances
4. Registers them in the importing module's typeclass environment

### 3. New Helper Functions

- **`module_name_to_path/1`** (Line 3387): Converts module names to file paths
  - `'Std.Show'` → `"lib/std/show.cure"`
  - `'Std.Core'` → `"lib/std/core.cure"`
  - Custom modules use lowercase path conversion

- **`register_module_typeclasses/2`** (Line 3406): Registers typeclass definitions from module items

- **`register_module_instances/2`** (Line 3427): Registers instance definitions from module items

## Usage Example

### Define a Typeclass in a Library Module

```cure
# lib/std/show.cure
module Std.Show do
  export [show/1]
  
  typeclass Show(T) do
    def show(x: T): String
  end
  
  instance Show(Int) do
    def show(x: Int): String = "<int>"
  end
  
  instance Show(String) do
    def show(x: String): String = x
  end
end
```

### Import and Use the Typeclass

```cure
# examples/show_test.cure
module ShowTest do
  import Std.Show [show/1]
  export [test_int/0]
  
  def test_int(): String =
    show(42)  # Resolves to Show(Int) instance
end
```

## How It Works

1. **Import Phase**: When `ShowTest` imports from `Std.Show`:
   - The type checker calls `check_import_items`
   - This triggers `import_module_typeclasses`
   - The `Std.Show` module is parsed
   - All typeclass definitions (Show) are registered
   - All instances (Show(Int), Show(String), etc.) are registered
   - The typeclass environment is updated

2. **Type Checking Phase**: When `show(42)` is encountered:
   - Type inference tries to resolve `show` as an identifier
   - Since it's not found as a regular function, `try_resolve_typeclass_method` is called
   - The method is found in the Show typeclass
   - The argument type is inferred as `Int`
   - The appropriate instance `Show(Int)` is resolved
   - Type checking succeeds with return type `String`

## Test Results

Comprehensive tests verify the system works:

1. **With Import**: ✓ Type checking succeeds
2. **Without Import**: ✓ Type checking fails with `unbound_variable: show`
3. **Show Module**: ✓ Parses and type checks successfully
   - 1 typeclass definition (Show)
   - 9 instance definitions (Int, Float, String, Bool, Atom, Charlist, List(Int), Option(Int), Result(Int, String))

## Files Modified

- **src/types/cure_typechecker.erl**: Added typeclass import functionality
  - Lines 3316-3450: New import system functions

## Files Created

- **test/show_module_test.erl**: Basic parsing and type checking test
- **test/typeclass_method_resolution_test.erl**: Comprehensive resolution test
- **docs/typeclass_import_system.md**: This documentation

## Architecture

```
Module A (User Code)
  import Std.Show [show/1]
         ↓
    Parse imports
         ↓
  import_module_typeclasses('Std.Show')
         ↓
    Parse lib/std/show.cure
         ↓
  Extract typeclasses & instances
         ↓
  Register in typeclass environment
         ↓
  Type check Module A with full typeclass context
```

## Benefits

1. **Modularity**: Typeclasses can be organized in library modules
2. **Reusability**: Standard typeclasses (Show, Eq, Ord) defined once, used everywhere
3. **Type Safety**: Full type checking with instance resolution
4. **Extensibility**: Users can add new instances in their own modules

## Future Enhancements

1. **Orphan Instance Detection**: Warn about instances defined outside the typeclass or type module
2. **Instance Import Control**: Selectively import only specific instances
3. **Typeclass Coherence**: Ensure only one instance per type per typeclass
4. **Performance**: Cache parsed module ASTs to avoid re-parsing on multiple imports
5. **Error Messages**: Improve error messages for missing instances or ambiguous resolution

## Related Documentation

- `docs/typeclass_status.md`: Comprehensive typeclass system status
- `docs/typeclass_implementation_progress.md`: Session progress tracking
- `TODO-2025-11-24.md`: Original issue list (item #2)
