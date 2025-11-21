# LSP Type Hole Remote Call Inference - Implementation

## Overview

This document describes the successful implementation of type inference for remote calls (imported functions) in the Cure LSP's type hole feature.

## Problem Statement

The LSP type hole feature needed to infer types for functions that use imported functions. For example:

```cure
import Std.List [map, filter]

def double_list(numbers: List(Int)): _ =
  map(numbers, fn(x) -> x * 2 end)
```

The `_` type hole should be inferred as `List(Int)` by analyzing the call to the imported `map/2` function.

## Solution Architecture

### Key Insight from `cure_typechecker`

After investigating `check_multiclause_function` in `cure_typechecker.erl`, we discovered that:

1. Multi-clause functions are checked by calling `check_single_clause_function` for each clause
2. Each clause check returns `{ok, NewEnv, Result}` with the function added to `NewEnv`
3. However, `check_multiclause_function` **discards** these environments and returns the original `Env`
4. This is intentional - the function signature is added during a separate "signature collection" pass

### Our Approach

To work around this, we:

1. **Extract imports from the module** - Parse the AST to find `import_def` records
2. **Build an enriched environment** - Add imported function types to the base environment
3. **Create a synthetic single-clause function** - For multi-clause functions, extract the first clause
4. **Call `check_function` directly** - This adds the function to the returned environment
5. **Extract the inferred type** - Look up the function in the returned environment and extract its return type

## Implementation Details

### Import Processing

```erlang
build_module_env(AST) when is_list(AST) ->
    % Extract module_def and its imports
    case [M || M <- AST, is_record(M, module_def)] of
        [#module_def{items = Items} | _] ->
            BaseEnv = cure_typechecker:builtin_env(),
            Imports = [Item || Item <- Items, is_record(Item, import_def)],
            process_imports_for_env(Imports, BaseEnv);
        ...
    end.
```

### Function Type Inference

For multi-clause functions (which is how the parser represents most functions):

```erlang
% Extract first clause
[FirstClause | _] = Clauses,
CheckParams = FirstClause#function_clause.params,
CheckBody = FirstClause#function_clause.body,
CheckReturnType = case is_type_hole(ReturnType) of 
    true -> undefined;  % Let type checker infer
    false -> ReturnType 
end,

% Create synthetic single-clause function
SyntheticFuncDef = #function_def{
    name = Name,
    params = CheckParams,
    return_type = CheckReturnType,
    body = CheckBody,
    clauses = undefined,  % Force single-clause checking
    ...
},

% Type check and extract result
{ok, NewEnv, {typecheck_result, true, ResultType, _, _}} = 
    cure_typechecker:check_function(SyntheticFuncDef, EnvWithImports),
FunType = cure_types:lookup_env(NewEnv, Name),
ReturnType = extract_return_type(FunType)
```

### Import Format Handling

The parser provides imports in two formats:

1. **Record format**: `#function_import{name = map, arity = 2}`
2. **Atom format**: Just `map` (without arity information)

For atom format imports, we default to arity 2 (common for stdlib functions like `map/2`, `filter/2`).

```erlang
import_single_item(Module, FunctionName, Env) when is_atom(FunctionName) ->
    Arity = 2,  % Default arity for stdlib functions
    FunctionType = create_imported_function_type(Module, FunctionName, Arity),
    NewEnv = cure_types:extend_env(Env, FunctionName, FunctionType),
    {ok, NewEnv}.
```

### Type Conversion

Internal type representations are converted to AST format for display:

```erlang
convert_type_to_ast_format({list_type, ElemType, _Length}) ->
    #dependent_type{
        name = 'List',
        type_params = [convert_type_to_ast_format(ElemType)],
        ...
    }.
```

## Results

The implementation successfully:

✅ Detects type holes in function return types  
✅ Extracts and processes module imports  
✅ Loads imported function types into the environment  
✅ Infers return types for functions using imported functions  
✅ Handles both single-clause and multi-clause functions  
✅ Reports type errors when inference fails  

### Example Output

For `examples/type_holes_demo.cure`:

```
Found 2 type holes:
  - '_' at line 12 (double_list)
    ✓ Inferred type: List(Int)
  
  - '_' at line 17 (process_data)  
    ✓ Inferred type: List(Int)
```

Both functions now correctly infer `List(Int)` with fully resolved type parameters!

## Files Modified

- `/opt/Proyectos/Ammotion/cure/lsp/cure_lsp_type_holes.erl` - Main implementation
  - `infer_function_return_type/2` - Core type inference logic
  - `build_module_env/1` - Import extraction and environment building
  - `process_imports_for_env/2` - Import processing pipeline
  - `import_single_item/3` - Individual import handling
  - `create_imported_function_type/3` - Type creation for imports

## Technical Challenges Overcome

1. **Multi-clause function handling** - Discovered that `check_multiclause_function` doesn't return the function in the environment
2. **Import format variations** - Handled both record and atom formats for imports
3. **Module structure** - Imports are stored in `items` list, not a separate field
4. **Type hole detection** - Distinguished type holes (`_`) from regular undefined types
5. **Environment threading** - Properly passed enriched environments through the type checking pipeline

## Future Improvements

1. **Arity inference** - Query modules for actual arities instead of defaulting to 2
2. **Caching** - Cache imported function types to avoid repeated lookups
3. **Error messages** - Provide more detailed error messages when type inference fails
4. **Type parameter inference** - Better handling of polymorphic type parameters in inferred types
5. **Multi-clause unification** - Unify types across all clauses instead of just using the first

## Testing

Test file: `/opt/Proyectos/Ammotion/cure/examples/type_holes_demo.cure`

The implementation has been tested with:
- Functions using `map/2` from `Std.List`
- Functions using `filter/2` from `Std.List`
- Multi-clause function definitions
- Both valid code (successful inference) and invalid code (expected errors)

## Conclusion

The LSP type hole feature now successfully infers types for functions that use imported functions, providing a complete Idris-style type hole experience in the Cure language.
