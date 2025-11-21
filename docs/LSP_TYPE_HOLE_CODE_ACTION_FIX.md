# LSP Type Hole Code Action Fix

## Problem
LSP code actions for type holes were not appearing in editors (Neovim, VS Code, etc.) even though:
- Type inference was working correctly
- Diagnostics were being generated
- The `generate_hole_code_actions/3` function was implemented and exported

## Root Cause
The diagnostic ranges were **incorrect** - they were using the **function definition location** instead of the **return type location**. This caused a mismatch when LSP clients requested code actions:

### Example
```cure
def double_list(numbers: List(Int)): _ =
  map(numbers, fn(x) -> x * 2 end)
```

The `_` is at column 40, but the diagnostic was reporting column 3 (where `def` starts), resulting in a range that didn't cover the actual underscore.

### Filter Logic
The LSP code action handler filters diagnostics to only include those where the **cursor is inside the diagnostic range**:

```erlang
OnSameLine = (CursorLine =:= DiagStartLine andalso CursorLine =:= DiagEndLine),
InsideRange = (CursorChar >= DiagStartChar andalso CursorChar =< DiagEndChar),
OnSameLine andalso InsideRange
```

When the user positioned their cursor on the `_` character and requested a code action, the filter would reject the diagnostic because the cursor wasn't within the incorrectly-positioned range.

## Solution
Modified `find_type_holes/1` in `cure_lsp_type_holes.erl` to use the **return type's location** instead of the function definition's location:

```erlang
% Before (incorrect - using function location)
case is_type_hole(RetType) of
    true ->
        HoleName = hole_name(RetType),
        [{HoleName, {return_type, Func}, Loc}];  % Loc from function_def
    ...
end

% After (correct - using return type location)
case is_type_hole(RetType) of
    true ->
        HoleName = hole_name(RetType),
        % Use the location from the return type itself
        HoleLoc = case RetType of
            #primitive_type{location = TypeLoc} when TypeLoc =/= undefined -> TypeLoc;
            _ -> Loc  % Fallback to function location
        end,
        [{HoleName, {return_type, Func}, HoleLoc}];
    ...
end
```

## Files Modified
- `/opt/Proyectos/Ammotion/cure/lsp/cure_lsp_type_holes.erl` (lines 97-103)
  - Modified `find_type_holes/1` to extract and use return type location

## Testing
Created `/opt/Proyectos/Ammotion/cure/lsp/test_code_actions.erl` to verify:

**Before fix:**
```
[TYPE_HOLES] Creating diagnostic: Line=12, Col=3
Diagnostic range: start=2, end=13
Cursor position: line=11, character=40
Cursor in range: false  ❌
Generated 0 actions
```

**After fix:**
```
[TYPE_HOLES] Creating diagnostic: Line=12, Col=40
Diagnostic range: start=39, end=50
Cursor position: line=11, character=40
Cursor in range: true  ✅
Generated 1 actions
```

## Usage in LSP
Now when users:
1. Write a function with a type hole: `def foo(x: Int): _ = x + 1`
2. Position cursor on the `_`
3. Trigger code actions (Ctrl+. in most editors)

They will see:
```
💡 Fill hole with: Int
```

And applying the action will replace `_` with the inferred type.

## Related Components
- Type inference: Working correctly since previous implementation
- Diagnostic generation: `generate_hole_diagnostics/2` 
- Code action generation: `generate_hole_code_actions/3`
- LSP integration: `handle_code_action/3` in `cure_lsp.erl`

## Parser Context
The Cure parser (`cure_parser.erl`) correctly tracks locations for:
- `#primitive_type{name, location}` - Type expressions including `_`
- `#function_def{..., return_type, location}` - Function definitions
- `#param{name, type, location}` - Function parameters

The fix simply ensures we use the right location from the AST.
