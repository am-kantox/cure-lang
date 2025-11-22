# Pipe Operator Result Handling

## Overview

The Cure pipe operator (`|>`) implements Railway-Oriented Programming with automatic `Result` type handling. This provides elegant error propagation and composition without explicit error checking at each step.

## Semantics

The pipe operator follows these rules:

### Rule 1: Bare Value Input
When a bare value `T` is piped, it's treated as `Ok(T)` for subsequent operations:
```cure
def double(x: Int): Int = x * 2
5 |> double  # Returns: Ok(10)
```

### Rule 2: `Ok(T)` Unwrapping
When `Ok(T)` flows through the pipe, the value is unwrapped before being passed to the transformation function:
```cure
def transformation_fun(x: Int): Int = x * 2
Ok(5) |> transformation_fun  # x receives 5 (unwrapped), returns Ok(10)
```

### Rule 3: `Error(E)` Propagation
When `Error(E)` flows through the pipe, transformation functions are **not called** and the error propagates to the end:
```cure
def transformation_fun(x: Int): Int = x * 2
Error("failed") |> transformation_fun  # Returns: Error("failed"), transformation_fun never called
```

### Rule 4: Result-Returning Functions
Transformation functions can return either bare values or `Result` types:
```cure
# Bare return - wrapped in Ok automatically
def double(x: Int): Int = x * 2
5 |> double  # Returns: Ok(10)

# Result return - used as-is
def safe_divide(x: Int): Result(Int, String) =
  match x do
    0 -> error("Cannot divide by zero")
    _ -> ok(10 / x)
  end

5 |> safe_divide  # Returns: Ok(2)
0 |> safe_divide  # Returns: Error("Cannot divide by zero")
```

### Rule 5: Chaining
Multiple pipes compose naturally with error short-circuiting:
```cure
def double(x: Int): Int = x * 2
def safe_divide(x: Int): Result(Int, String) = ...

5 |> double |> safe_divide  
# Flow: 5 -> Ok(10) -> Ok(1)

0 |> safe_divide |> double
# Flow: 0 -> Error("Cannot divide by zero") -> Error(...) (double not called)
```

### Rule 6: Final Return Type
The entire pipe chain **always** returns `Result(T, E)`:
```cure
def f(): Result(Int, String) = 5 |> double  # Must declare Result return type
```

## Implementation

The pipe operator is implemented through:

1. **Parser** (`src/parser/cure_parser.erl`): Parses `|>` as a binary operator
2. **Codegen** (`src/codegen/cure_codegen.erl`): Generates `monadic_pipe_call` instructions
3. **Runtime** (`src/runtime/cure_std.erl`): The `pipe/2` function handles all cases

### Runtime Implementation

```erlang
% cure_std.erl
pipe({'Error', _} = Err, _RHO) ->
    % Rule 1: propagate error without calling RHO
    Err;
pipe({'Ok', V}, RHO) when is_function(RHO) ->
    % Rule 2: unwrap Ok(V), call RHO(V), wrap result if not already a monad
    try
        Res = RHO(V),
        case is_monad(Res) of
            true -> Res;
            false -> {'Ok', Res}
        end
    catch
        Error:Reason -> {'Error', {pipe_runtime_error, Error, Reason}}
    end;
pipe(LHO, RHO) when is_function(RHO) ->
    % Rule 3: pass bare LHO to RHO, wrap result if not already a monad
    try
        Res = RHO(LHO),
        case is_monad(Res) of
            true -> Res;
            false -> {'Ok', Res}
        end
    catch
        Error:Reason -> {'Error', {pipe_runtime_error, Error, Reason}}
    end.
```

## Examples

See `examples/simple_pipe.cure` for comprehensive examples:

```cure
module simple_pipe do
  export [
    example_bare_to_bare/0,
    example_bare_to_result/0,
    example_result_ok_chain/0,
    example_result_error_propagation/0,
    example_mixed_chain/0
  ]
  
  import Std.Core [Result, ok/1, error/1]

  # Example 1: Bare -> Bare
  def double(x: Int): Int = x * 2
  def example_bare_to_bare(): Result(Int, String) =
    5 |> double  # Returns: Ok(10)

  # Example 2: Bare -> Result
  def safe_divide(x: Int): Result(Int, String) =
    match x do
      0 -> error("Cannot divide by zero")
      _ -> ok(10 / x)
    end
  def example_bare_to_result(): Result(Int, String) =
    5 |> safe_divide  # Returns: Ok(2)

  # Example 3: Chaining with Ok
  def example_result_ok_chain(): Result(Int, String) =
    5 |> double |> safe_divide  # Returns: Ok(1)

  # Example 4: Error propagation
  def example_result_error_propagation(): Result(Int, String) =
    0 |> safe_divide |> double  # Returns: Error("Cannot divide by zero")

  # Example 5: Mixed chain
  def increment(x: Int): Int = x + 1
  def example_mixed_chain(): Result(Int, String) =
    5 |> double |> increment |> safe_divide  # Returns: Ok(0)
end
```

## Testing

Run the test suite with:
```bash
erl -pa _build/ebin -noshell -s simple_pipe_test run
```

All tests verify:
- ✓ Bare value → Bare function returns `Ok(result)`
- ✓ Bare value → Result function preserves Result
- ✓ Error returns propagate `Error` unchanged
- ✓ Chaining bare functions works correctly
- ✓ Error propagation short-circuits the chain
- ✓ Mixed bare and Result functions compose properly

## Benefits

1. **Railway-Oriented Programming**: Errors flow on a separate "track"
2. **No Explicit Error Checking**: No need for `match` or `case` at every step
3. **Composability**: Functions compose naturally regardless of return type
4. **Type Safety**: All pipes return `Result`, making error handling explicit
5. **Short-Circuiting**: Errors stop execution immediately, avoiding wasted work

## Related

- `Std.Core.Result(T, E)` - Result type definition
- `Std.Core.ok/1` - Wrap value in Ok
- `Std.Core.error/1` - Wrap value in Error
- `Std.Core.and_then/2` - Monadic bind for manual composition
- `Std.Core.map_ok/2` - Map function over Ok values
