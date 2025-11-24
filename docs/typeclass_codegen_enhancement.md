# Typeclass Method Resolution in Codegen - Enhancement

## Date
November 24, 2024

## Overview
Enhanced the codegen to properly resolve typeclass method calls to instance implementations, even without explicit typeclass constraints in the where clause.

## Problem
Previously, typeclass method resolution in codegen only worked when there were explicit typeclass constraints (e.g., `where Show(T)`). For direct method calls like `show(42)` in modules that import typeclasses, the resolution would fail.

## Solution
Added a new function `try_resolve_direct_typeclass_call/3` that:
1. Checks if a function call is a known typeclass method
2. Infers the concrete type from the arguments
3. Generates the correct mangled instance method name (e.g., `Show_Int_show`)
4. Resolves the call to the instance implementation

## Implementation Details

### Files Modified
- **src/codegen/cure_codegen.erl**: Lines 2877-2989

### Key Functions

#### `try_resolve_typeclass_method/3` (Enhanced)
```erlang
try_resolve_typeclass_method(Function, Args, State) ->
    case State#codegen_state.typeclass_constraints of
        [] ->
            % NEW: Check for direct typeclass method calls
            try_resolve_direct_typeclass_call(Function, Args, State);
        Constraints ->
            % Existing constraint-based resolution
            ...
    end.
```

#### `try_resolve_direct_typeclass_call/3` (New)
Handles direct typeclass method calls without constraints:
- Maps method names to typeclasses (show → Show, eq → Eq, etc.)
- Infers concrete types from literal arguments
- Generates mangled instance method names
- Returns resolved function identifiers

#### `is_known_typeclass_method/1` (New)
Maps method names to their typeclasses:
```erlang
KnownMethods = #{
    show => 'Show',
    eq => 'Eq',
    compare => 'Ord',
    ...
}
```

## Test Results

### Test 1: Direct Method Call ✅
**Input:** `show(42)`

**Generated Instructions:**
```erlang
{beam_instr, load_global, ['Show_Int_show'], undefined}
{beam_instr, load_literal, [42], undefined}
{beam_instr, call, [1], undefined}
```

**Result:** ✅ Successfully resolved to `Show_Int_show`

### Test 2: Full Module Compilation
**Status:** Partial - Core resolution works, full pipeline needs more work

The codegen correctly resolves method calls, but full module compilation with imports needs additional integration work.

## Current Capabilities

✅ **Working:**
- Type inference: Resolves `show` as a typeclass method
- Import system: Loads typeclasses from imported modules
- **Codegen resolution:** Generates correct instance method names
- Method dispatch: Creates proper function calls

⚠️ **Partial:**
- Full module compilation with typeclass imports
- Instance registration and module loading

## Example Usage

### Input Code
```cure
module ShowTest do
  import Std.Show [show/1]
  export [test/0]
  
  def test(): String =
    show(42)  # Resolves to Show_Int_show
end
```

### Generated BEAM Instructions (for show(42))
```erlang
load_global('Show_Int_show')  % Load the instance method
load_literal(42)              % Load the argument
call(1)                       % Call the method
```

## Integration Status

| Component | Status | Notes |
|-----------|--------|-------|
| Lexer | ✅ Complete | Keywords recognized |
| Parser | ✅ Complete | Typeclass/instance parsing |
| Type Checker | ✅ Complete | Import system, method resolution |
| **Codegen (Method Resolution)** | ✅ **Complete** | Generates correct instance calls |
| Codegen (Full Pipeline) | ⚠️ Partial | Module compilation needs work |
| Runtime | ⚠️ Partial | Instance dispatch needs implementation |
| Tests | ✅ Complete | Resolution verified |

## Next Steps

1. **Complete Module Compilation Pipeline**
   - Fix module compilation with typeclass imports
   - Ensure instance methods are included in compiled modules
   - Handle cross-module instance calls

2. **Runtime Instance Dispatch**
   - Implement `cure_instance_registry` for runtime lookup
   - Add automatic instance registration on module load
   - Support dynamic dispatch for polymorphic calls

3. **Instance Code Generation**
   - Ensure instance definitions compile to proper Erlang functions
   - Generate export lists for instance methods
   - Create module attributes for typeclass metadata

4. **End-to-End Testing**
   - Compile complete modules with typeclasses
   - Generate executable BEAM files
   - Test runtime execution of typeclass methods

## Architecture

```
User Code: show(42)
      ↓
Parser: Parses as function_call_expr
      ↓
Type Checker: Resolves as Show typeclass method
      ↓
Codegen: try_resolve_direct_typeclass_call
      ↓
  is_known_typeclass_method(show) → {true, 'Show'}
  infer_type_from_arg([42]) → {ok, 'Int'}
  Generate: 'Show_Int_show'
      ↓
BEAM Instructions:
  load_global('Show_Int_show')
  load_literal(42)
  call(1)
      ↓
Runtime: Execute Show_Int_show(42)
```

## Known Limitations

1. **Type Inference:** Currently only infers types from literal values
   - `show(42)` works (literal integer)
   - `show(x)` might not resolve correctly (variable)
   
2. **Known Methods:** Hardcoded list of typeclass methods
   - Should be dynamically populated from imported modules
   - Currently limited to: show, eq, compare, fmap, bind, etc.

3. **Cross-Module Calls:** Resolution assumes local or imported instances
   - Need module-qualified calls for external instances
   - Instance registry not fully integrated

## Files Created

- **test/typeclass_codegen_test.erl**: Codegen resolution tests
- **docs/typeclass_codegen_enhancement.md**: This documentation

## Related Documentation

- `docs/typeclass_import_system.md`: Import system implementation
- `docs/typeclass_status.md`: Overall typeclass system status
- `TODO-2025-11-24.md`: Original TODO list
