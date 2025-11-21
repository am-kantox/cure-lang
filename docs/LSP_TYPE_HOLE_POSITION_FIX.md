# LSP Type Hole Code Action Position Fix

## Problem
Code actions for type holes were inserting the inferred type at the wrong position, resulting in malformed code:

**Before fix:**
```cure
def process_data(xs: List(Int)): _ =
```

**After applying code action (WRONG):**
```cure
def process_data(xs: List(Int)): _ =List(Int)
```

The type was being inserted **after** the `=` instead of **replacing** the `_`.

## Root Cause
In `create_fill_hole_action` (lines 579-620 in `cure_lsp_type_holes.erl`), the code was using a "rough estimate" to calculate the underscore position:

```erlang
% OLD CODE (incorrect)
UnderscoreChar = StartChar + 4,  % Rough estimate
ActualRange = #{
    start => #{line => StartLine, character => UnderscoreChar},
    'end' => #{line => StartLine, character => UnderscoreChar + 1}
},
```

### Why This Was Wrong

1. The diagnostic range is created as `(Col - 1)` to `(Col + 10)` where `Col` is the 1-indexed parser column
2. This converts to 0-indexed LSP coordinates: `StartChar = Col - 1`
3. So `StartChar` is **already** the correct 0-indexed position of the underscore
4. Adding 4 to it (`StartChar + 4`) was shifting the replacement position 4 characters too far right

### Example
For line `  def double_list(numbers: List(Int)): _ =`:
- Parser reports `Col = 40` (1-indexed)
- Diagnostic creates `StartChar = 39` (0-indexed LSP coordinate)
- **Incorrect calculation**: `UnderscoreChar = 39 + 4 = 43` ❌
  - Position 43 is the space after `=`
  - Results in: `): _ =List(Int)`
- **Correct position**: `39` ✅
  - Position 39 is the `_`
  - Results in: `): List(Int) =`

## Solution
Removed the incorrect `+4` offset and used `StartChar` directly:

```erlang
% NEW CODE (correct)
% The diagnostic range was created as (Col-1) to (Col+10) in 0-indexed LSP coordinates
% where Col is the 1-indexed parser column of the underscore.
% So StartChar is already the correct 0-indexed position of the underscore.
% We want to replace exactly one character: the underscore itself.
ActualRange = #{
    start => #{line => StartLine, character => StartChar},
    'end' => #{line => StartLine, character => StartChar + 1}
},
```

## Files Modified
- `/opt/Proyectos/Ammotion/cure/lsp/cure_lsp_type_holes.erl` (lines 589-602)
  - Removed incorrect `UnderscoreChar = StartChar + 4` calculation
  - Changed `ActualRange` to use `StartChar` directly

## Verification

### Test Output Before Fix
```
Diagnostic range: start=39, end=50
Replacement range: start=43, end=44  ❌ (4 characters off)
```

### Test Output After Fix
```
Diagnostic range: start=39, end=50
Replacement range: start=39, end=40  ✅ (correct!)
```

### Character Position Verification
```python
line = '  def double_list(numbers: List(Int)): _ ='
#       0123456789012345678901234567890123456789012
#                 1111111111222222222233333333334444

line[39] == '_'  # True ✅
```

## Result
Now when applying the code action:

**Before:**
```cure
def double_list(numbers: List(Int)): _ =
```

**After (correct):**
```cure
def double_list(numbers: List(Int)): List(Int) =
```

The type hole `_` is correctly replaced with the inferred type `List(Int)`.

## Related Fixes
This completes the type hole code action implementation, building on:
1. Remote call type inference implementation
2. Diagnostic location tracking fix (`LSP_TYPE_HOLE_CODE_ACTION_FIX.md`)
3. Makefile fix for LSP compilation (`MAKE_LSP_FIX.md`)
