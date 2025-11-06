# Cure Compiler Performance Regression Analysis

## Summary

Identified a **massive performance regression** in the Cure compiler's type checking phase that causes 56-58% of compilation time to be spent in standard library loading.

## Profiling Results

### Simple Test File (`profile_test.cure` - 5 lines)
```
Total Time: 17.976 ms
Breakdown:
  Lexer:       1.196 ms (6.7%)
  Parser:      3.094 ms (17.2%)
  Type Check: 10.228 ms (56.9%)  ← BOTTLENECK
  Codegen:     3.458 ms (19.2%)
```

### Realistic File (`01_list_basics.cure` - 41 lines with 3 imports)
```
Total Time: 27.690 ms
Breakdown:
  Lexer:       1.418 ms (5.1%)
  Parser:      4.190 ms (15.1%)
  Type Check: 16.079 ms (58.1%)  ← BOTTLENECK
  Codegen:     6.003 ms (21.7%)
```

### Detailed Profiling (fprof)
```
get_stdlib_function_type: 233ms out of 247ms type checking (94%!)
  ↓
load_stdlib_modules: Parses ALL stdlib .cure files
  ↓
cure_parser:parse_file: Called for EVERY stdlib file
```

## Root Cause

**File**: `src/types/cure_typechecker.erl`  
**Function**: `load_stdlib_modules()` (lines 1447-1472)  
**Problem**: `cure_parser:parse_file()` (line 1464)

### The Issue

On the **first import** of any stdlib module:

1. Lists all files in `lib/std/` directory
2. **Parses EVERY .cure file** in the stdlib directory
3. Extracts function signatures from all modules
4. Caches in process dictionary

### Why This is Slow

- Parsing is expensive (involves lexing + full AST construction)
- Happens on EVERY compilation
- For stdlib with ~15+ modules, this means parsing 15+ files for every compilation
- Even though results are cached, the cache is per-process (lost between compilations)

## Example Trace

```erlang
% User code:
import Std.List [map/2, filter/2, fold/3]

% What happens internally:
1. check_import -> import_items -> import_item
2. get_stdlib_function_type('Std.List', map, 2)
3. Cache miss → load_stdlib_modules()
4. file:list_dir("lib/std/") → [core.cure, list.cure, io.cure, ...]
5. FOR EACH FILE:
   - cure_parser:parse_file("lib/std/core.cure")    ← EXPENSIVE
   - cure_parser:parse_file("lib/std/list.cure")    ← EXPENSIVE
   - cure_parser:parse_file("lib/std/io.cure")      ← EXPENSIVE
   - ... (15+ files)
   - extract_module_functions(AST)
6. Cache results in process dictionary
7. Return type for map/2
```

## Impact

For a file with 3 imports from different stdlib modules:
- **233ms** spent in stdlib loading (94% of type checking)
- **16ms** total type checking time (58% of compilation)
- For comparison: lexing takes 1.4ms, parsing takes 4.2ms

**This is a 50-100x slowdown** compared to what it should be.

## Recommended Solutions

### Solution 1: Pre-compiled Type Signatures (Best)
**Effort**: Medium  
**Impact**: Eliminates parsing completely

```erlang
% Generate at build time:
lib/std/.type_signatures.erl
-module(std_type_signatures).
-export([get_function_type/3]).

get_function_type('Std.List', map, 2) ->
    {function_type, [...], ...};
get_function_type('Std.List', filter, 2) ->
    {function_type, [...], ...};
...
```

Benefits:
- Zero parsing overhead
- Types available instantly
- Can be version-controlled
- Works across processes

### Solution 2: Lazy Module Loading (Good)
**Effort**: Low  
**Impact**: ~85% improvement

Only parse the specific module being imported:

```erlang
load_stdlib_module(ModuleName) ->
    FilePath = "lib/std/" ++ module_to_filename(ModuleName),
    case cure_parser:parse_file(FilePath) of
        {ok, AST} -> extract_module_functions(AST);
        {error, _} -> #{}
    end.
```

Benefits:
- Only pays cost for imported modules
- Simple to implement
- Backward compatible

### Solution 3: Persistent Cache (Good)
**Effort**: Medium  
**Impact**: ~95% improvement (after first compilation)

Use ETS or disk cache:

```erlang
-define(STDLIB_CACHE, stdlib_type_cache).

init_stdlib_cache() ->
    case ets:info(?STDLIB_CACHE) of
        undefined ->
            ets:new(?STDLIB_CACHE, [named_table, public, set]),
            load_and_cache_stdlib();
        _ ->
            ok
    end.
```

Benefits:
- Fast after first load
- Survives multiple compilations
- Can be invalidated on stdlib changes

### Solution 4: Parallel Loading
**Effort**: Medium  
**Impact**: ~70% improvement

Parse stdlib files in parallel:

```erlang
load_stdlib_files_parallel(BasePath, Files) ->
    Tasks = [fun() -> parse_stdlib_file(BasePath ++ F) end || F <- Files],
    Results = pmap(Tasks),
    merge_results(Results).
```

Benefits:
- Uses multi-core
- Reduces wall-clock time
- Can combine with other solutions

## Recommended Implementation Plan

1. **Immediate (Solution 2)**: Implement lazy loading - quick win
2. **Short-term (Solution 1)**: Generate pre-compiled signatures at build time
3. **Optional (Solution 3)**: Add persistent caching for development workflow

## Files to Modify

1. `src/types/cure_typechecker.erl`:
   - `load_stdlib_modules/0` (line 1447)
   - `get_stdlib_function_type/3` (line 1603)
   - `load_stdlib_files/3` (line 1460)

2. `Makefile`:
   - Add target to generate type signatures

3. New file: `scripts/generate_type_signatures.escript`:
   - Parse stdlib and generate signatures file

## Expected Performance After Fix

With lazy loading:
```
Type Check: 16.079 ms → ~2-3 ms (85% reduction)
Total:      27.690 ms → ~13-14 ms (50% improvement)
```

With pre-compiled signatures:
```
Type Check: 16.079 ms → ~0.5-1 ms (95% reduction)
Total:      27.690 ms → ~11-12 ms (55% improvement)
```

## Verification

Run profiling again after fix:
```bash
escript profile_compile.erl examples/01_list_basics.cure
escript profile_detailed.erl examples/01_list_basics.cure
```

Expected to see `get_stdlib_function_type` drop from 233ms to <5ms.
