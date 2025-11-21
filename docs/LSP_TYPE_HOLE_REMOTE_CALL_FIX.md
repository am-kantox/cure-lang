# LSP Type Hole Remote Call Inference Fix

## Problem

The LSP was unable to infer types for functions that use imported functions (remote calls) in their body when using type holes (`_`). For example:

```cure
module TypeHolesDemo do
  import Std.List [map, filter]
  
  # LSP showed "Cannot infer type" for this:
  def double_list(numbers: List(Int)): _ =
    map(numbers, fn(x) -> x * 2 end)
end
```

The compiler worked fine, but the LSP couldn't infer that the return type should be `List(Int)`.

## Root Cause

The LSP's type hole inference module (`lsp/cure_lsp_type_holes.erl`) had its own simplified type inference that:

1. **Didn't process imports**: The simple `infer_expr_type/1` function didn't build a proper environment with imported functions
2. **Had hardcoded special cases**: Only `map` was special-cased, and even that was limited
3. **Didn't use the real type checker**: Instead of leveraging `cure_typechecker:infer_type/2`, it reimplemented a subset of type inference

## Solution

Updated `lsp/cure_lsp_type_holes.erl` to use the full Cure type checker:

### 1. Build Proper Type Environment

```erlang
build_module_env(AST) when is_list(AST) ->
    BaseEnv = cure_typechecker:builtin_env(),
    % Find import definitions in the AST
    Imports = [Item || Item <- AST, is_record(Item, import_def)],
    % Process imports to extend environment
    process_imports_for_env(Imports, BaseEnv).
```

### 2. Process Imports

```erlang
import_single_item(Module, #function_import{name = Name, arity = Arity}, Env) ->
    % Use cure_typechecker's function to get the imported function type
    FunctionType = cure_typechecker:create_imported_function_type(Module, Name, Arity),
    NewEnv = cure_types:extend_env(Env, Name, FunctionType),
    {ok, NewEnv}.
```

This leverages `cure_stdlib_signatures` to get the exact type signatures for imported functions like:
- `map: (List(T), T => U) -> List(U)`
- `filter: (List(T), T => Bool) -> List(T)`

### 3. Use Full Type Checker

```erlang
infer_function_return_type(#function_def{body = Body, params = Params}, AST) ->
    case build_module_env(AST) of
        {ok, Env} ->
            EnvWithParams = add_params_to_env(Params, Env),
            % Use cure_typechecker to infer the body type
            case cure_typechecker:infer_type(Body, EnvWithParams) of
                {ok, Type} -> 
                    {ok, convert_type_to_ast_format(Type)};
                {error, _} = Error -> 
                    Error
            end;
        {error, _} = Error ->
            Error
    end.
```

### 4. Convert Types

Added `convert_type_to_ast_format/1` to convert from the type checker's internal representation to the AST format expected by the LSP:

```erlang
convert_type_to_ast_format({list_type, ElemType, _Length}) ->
    #dependent_type{
        name = 'List',
        type_params = [convert_type_to_ast_format(ElemType)],
        value_params = [],
        location = undefined
    }.
```

## Benefits

1. **Complete Coverage**: Works for all imported functions, not just hardcoded cases
2. **Consistency**: LSP and compiler use the same type inference logic
3. **Future-Proof**: Automatically supports new standard library functions
4. **Accurate**: Uses the same constraint solving and unification as the compiler

## Testing

The fix has been tested with:

1. **Basic remote calls**: `map(numbers, fn(x) -> x * 2 end)` correctly infers `List(Int)`
2. **Multiple imports**: Both `map` and `filter` work correctly
3. **Chained operations**: Combining multiple imported functions works
4. **Type holes**: Both return type holes and parameter type holes are supported

## Files Changed

- `lsp/cure_lsp_type_holes.erl`: Main implementation
  - Added `build_module_env/1` to build environment with imports
  - Added `process_imports_for_env/2` to process import statements
  - Added `import_single_item/3` to add imported functions to environment
  - Added `add_params_to_env/2` to add parameters to environment
  - Added `convert_type_to_ast_format/1` for type conversion
  - Updated `infer_function_return_type/2` to use full type checker

## Related

- Compiler already had correct implementation in `src/types/cure_typechecker.erl`
- Type signatures in `src/types/cure_stdlib_signatures.erl` are shared between compiler and LSP
- No changes needed to the core type system
