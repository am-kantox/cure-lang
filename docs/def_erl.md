# def_erl: Erlang Interoperability in Cure

## Overview

The `def_erl` feature provides seamless interoperability between Cure and Erlang by allowing you to embed raw Erlang code directly in Cure functions. This enables you to leverage the entire Erlang ecosystem while maintaining type safety at the Cure level.

## Syntax

```cure
def_erl function_name(param1: Type1, param2: Type2): ReturnType =
  raw_erlang_code.
```

### Key Requirements

1. **Explicit Return Type**: `def_erl` functions MUST have an explicit return type annotation
2. **Raw Erlang Body**: The function body contains raw Erlang code as a string
3. **Type Trust**: The type checker trusts your type annotations without analyzing the Erlang code

## Examples

### Basic Erlang Functions

```cure
module ErlangInterop do
  # Simple Erlang built-in functions
  def_erl erlang_length(list: List(T)): Int =
    length(list).

  def_erl erlang_reverse(list: List(T)): List(T) =
    lists:reverse(list).

  # Erlang module calls
  def_erl erlang_timestamp(): Int =
    erlang:system_time().
end
```

### Complex Erlang Expressions

```cure
module ComplexErlang do
  # Case expressions and pattern matching
  def_erl safe_divide(x: Float, y: Float): Result(Float, String) =
    case Y of
        0.0 -> error("Division by zero");
        _ -> 
            Result = X / Y,
            Result
    end.

  # Mathematical operations
  def_erl complex_math(x: Float, y: Float): Float =
    X / Y + math:sin(X) * math:cos(Y).

  # String operations
  def_erl format_string(template: String, args: List(String)): String =
    io_lib:format(template, args).
end
```

### Using def_erl Functions

Once defined, `def_erl` functions can be used like regular Cure functions:

```cure
module Usage do
  def demo(): Unit =
    let my_list = [1, 2, 3, 4, 5]
    let length = erlang_length(my_list)        # Returns 5
    let reversed = erlang_reverse(my_list)     # Returns [5, 4, 3, 2, 1]
    let timestamp = erlang_timestamp()         # Returns current timestamp
    
    print("Length: " ++ int_to_string(length))
    print("Reversed: " ++ list_to_string(reversed))
end
```

## Type Safety

### Trust-Based Type Checking

`def_erl` functions use a **trust-based type system**:

- ✅ **Parameter types** are enforced when calling the function
- ✅ **Return type** is trusted as specified in the annotation
- ⚠️ **Function body** is NOT type-checked (raw Erlang)

### Best Practices

1. **Be Accurate with Types**: Ensure your return type annotation matches what the Erlang code actually returns
2. **Test Thoroughly**: Since the body isn't type-checked, test your `def_erl` functions extensively
3. **Use for Interop**: Prefer `def_erl` for calling existing Erlang libraries, not for general programming

### Type Mapping

| Cure Type | Erlang Type | Example |
|-----------|-------------|---------|
| `Int` | `integer()` | `42` |
| `Float` | `float()` | `3.14` |
| `String` | `binary()` | `<<"hello">>` |
| `List(T)` | `[T]` | `[1, 2, 3]` |
| `Result(T, E)` | `{ok, T} \| {error, E}` | `{ok, value}` |

## Implementation Details

### Compilation Pipeline

1. **Lexer**: Recognizes `def_erl` keyword
2. **Parser**: Creates `erlang_function_def` AST nodes with raw Erlang body
3. **Type Checker**: Trusts type annotations, skips body analysis
4. **Code Generator**: Emits functions with raw Erlang code preserved
5. **BEAM Compiler**: Converts to proper Erlang abstract forms

### AST Representation

```erlang
-record(erlang_function_def, {
    name :: atom(),
    params :: [param()],
    return_type :: type_expr(),
    constraint :: expr() | undefined,
    erlang_body :: string(),  % Raw Erlang code
    location :: location()
}).
```

## Common Patterns

### Error Handling

```cure
module ErrorHandling do
  def_erl safe_file_read(filename: String): Result(String, String) =
    case file:read_file(Filename) of
        {ok, Content} -> {ok, Content};
        {error, Reason} -> {error, atom_to_list(Reason)}
    end.
end
```

### List Processing

```cure
module ListOps do
  def_erl parallel_map(func: Fun(T, U), list: List(T)): List(U) =
    lists:map(func, list).

  def_erl list_comprehension(list: List(Int)): List(Int) =
    [X * 2 || X <- list, X > 0].
end
```

### Process Operations

```cure
module ProcessOps do
  def_erl spawn_process(func: Fun(Unit, Unit)): ProcessId =
    spawn(func).

  def_erl send_message(pid: ProcessId, msg: T): Unit =
    pid ! msg.
end
```

## Limitations

1. **No Type Checking of Body**: Erlang code is not analyzed by Cure's type checker
2. **Syntax Restrictions**: Must use valid Erlang syntax in the body
3. **Import Handling**: Erlang modules must be available at runtime
4. **Debugging**: Error messages will be from Erlang, not Cure

## Migration Guide

### From Pure Cure to def_erl

```cure
# Before: Pure Cure (limited)
def length(list: List(T)): Int =
  # Would need to implement recursively
  match list do
    [] -> 0
    [_ | rest] -> 1 + length(rest)
  end

# After: Using def_erl (efficient)
def_erl length(list: List(T)): Int =
  length(list).
```

### From Erlang to def_erl

```erlang
% Before: Pure Erlang
-module(my_module).
-export([process_data/1]).

process_data(Data) ->
    lists:map(fun(X) -> X * 2 end, Data).
```

```cure
# After: Cure with def_erl
module MyModule do
  export [process_data/1]
  
  def_erl process_data(data: List(Int)): List(Int) =
    lists:map(fun(X) -> X * 2 end, data).
end
```

## Future Enhancements

- **Type Bridge Generation**: Automatically generate type conversions
- **Erlang Module Import**: Direct import of Erlang modules with type signatures
- **FFI Macros**: Macros for common interop patterns
- **Runtime Type Validation**: Optional runtime type checking for `def_erl` functions

## Conclusion

`def_erl` bridges the gap between Cure's safety and Erlang's ecosystem, enabling:

- ✅ **Gradual Migration**: Move from Erlang to Cure incrementally
- ✅ **Library Access**: Use existing Erlang libraries seamlessly  
- ✅ **Performance**: Leverage optimized Erlang code where needed
- ✅ **Interoperability**: Mix Cure and Erlang code in the same project

Use `def_erl` wisely for interoperability, while preferring pure Cure for new, type-safe code.