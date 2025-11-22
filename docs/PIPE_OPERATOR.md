# Pipe Operator (`|>`)

The pipe operator (`|>`) is a fundamental feature of Cure that provides elegant error handling and function composition through monadic semantics with automatic Result type management.

## Table of Contents

- [Overview](#overview)
- [Syntax](#syntax)
- [Semantics](#semantics)
- [Type System Integration](#type-system-integration)
- [Examples](#examples)
- [Implementation Details](#implementation-details)
- [Best Practices](#best-practices)
- [Comparison with Other Languages](#comparison-with-other-languages)

## Overview

The pipe operator enables you to write data transformation pipelines in a readable, left-to-right flow while automatically handling error propagation. It combines the ergonomics of Elixir's pipe operator with the safety of Rust's `?` operator.

### Key Features

- **Automatic Error Propagation**: Errors short-circuit the pipeline without requiring explicit checks
- **Result Type Wrapping**: Non-monadic values are automatically wrapped in `Ok()`
- **Exception Safety**: Runtime exceptions are caught and converted to `Error()` values
- **Clean Syntax**: Write sequential transformations without nesting or intermediate variables

## Syntax

```cure
expression |> function
expression |> function(arg1, arg2)
```

The pipe operator has the lowest precedence (1) and left associativity, meaning:

```cure
a |> b |> c  # Parsed as: (a |> b) |> c
1 + 2 |> f   # Parsed as: (1 + 2) |> f
```

## Semantics

The pipe operator implements three fundamental rules:

### Rule 1: Error Propagation

```cure
Error(reason) |> function
# => Error(reason)  # function is NOT called
```

If the left-hand side is an `Error`, the entire pipeline stops and the error is propagated without calling the function.

### Rule 2: Ok Unwrapping

```cure
Ok(value) |> function
# => Ok(function(value))  # value is unwrapped before calling function
```

If the left-hand side is `Ok(value)`, the value is extracted, passed to the function, and the result is wrapped in `Ok()` (unless the function already returns a Result type).

### Rule 3: Value Passing

```cure
value |> function
# => Ok(function(value))  # value is passed directly, result is wrapped
```

If the left-hand side is a plain value (not a Result type), it's passed to the function and the result is wrapped in `Ok()`.

### Exception Handling

If a function in the pipeline throws an exception, it's automatically caught and converted to an Error:

```cure
Ok(0) |> (fun(x) -> 1 / x)
# => Error({pipe_runtime_error, error, badarith})
```

## Type System Integration

The type checker understands the pipe operator and performs proper type inference:

```cure
def process_data(input: String) -> Result(Int, String) do
  input
    |> parse_int       # String -> Result(Int, String)
    |> validate_range  # Int -> Result(Int, String) 
    |> double          # Int -> Int (automatically wrapped)
end
```

Type inference ensures:
- The piped value's type matches the function's first parameter
- Result types are properly propagated through the chain
- Non-monadic return values are wrapped in Result<T>

## Examples

### Basic Piping

```cure
def example1(): Result(Int, String) =
  5
  |> double      # 10
  |> increment   # 11
  # Result: Ok(11)

def double(x: Int) -> Int = x * 2
def increment(x: Int) -> Int = x + 1
```

### Error Handling

```cure
def parse_and_process(input: String) -> Result(String, String) do
  input
    |> parse_data        # Returns Error if invalid
    |> validate          # Only runs if parse succeeded
    |> transform         # Only runs if validate succeeded
    |> format_output     # Only runs if transform succeeded
end
```

### Piping with Arguments

The piped value becomes the first argument:

```cure
def example2(): Result(Int, String) =
  10
  |> add(5)       # add(10, 5) => 15
  |> multiply(3)  # multiply(15, 3) => 45
  # Result: Ok(45)

def add(x: Int, y: Int) -> Int = x + y
def multiply(x: Int, y: Int) -> Int = x * y
```

### Real-World Example

```cure
def process_user_input(input: String): Result(User, String) do
  input
  |> trim_whitespace
  |> validate_email
  |> normalize_email
  |> check_not_taken
  |> create_user
```

### Error Recovery

```cure
def safe_divide(x: Int, y: Int): String =
  let result = x |> divide_by(y)
  match result do
    Ok(value) -> "Result: " <> show(value)
    Error(reason) -> "Error: " <> reason
  end
```

### Combining Operators

```cure
def complex_computation(): Result(String, String) =
  (calculate_base() + 10)
  |> apply_discount
  |> format_price
```

## Implementation Details

### Lexer

The pipe operator is tokenized as a two-character operator:

```erlang
<<"|>">> => '|>'
```

### Parser

The operator is parsed with:
- **Precedence**: 1 (lowest)
- **Associativity**: left

This ensures pipes are evaluated left-to-right and have lower precedence than all other operations.

### Code Generation

The compiler generates a `monadic_pipe_call` instruction that is translated to BEAM bytecode as a call to `cure_std:pipe/2`:

```erlang
generate_monadic_pipe_form(Function, PipedValue, RestArgs, Line)
```

This creates Erlang code that:
1. Wraps the piped value with `ok()` if not already a Result
2. Checks if it's `Ok(value)` or `Error(reason)`
3. If Ok, unwraps and calls the function
4. If Error, propagates without calling the function
5. Wraps non-monadic results in `Ok()`

### Runtime

The runtime function `cure_std:pipe/2` implements the three semantic rules:

```erlang
pipe({'Error', _} = Err, _RHO) -> Err;  % Rule 1
pipe({'Ok', V}, RHO) -> wrap_result(RHO(V));  % Rule 2
pipe(LHO, RHO) -> wrap_result(RHO(LHO)).  % Rule 3
```

## Best Practices

### Do: Use for Sequential Transformations

```cure
# Good: Clear data flow
  input
  |> step1
  |> step2
  |> step3
```

### Don't: Overuse in Simple Cases

```cure
# Bad: Overkill for single operation
value |> function

# Better: Direct call
function(value)
```

### Do: Handle Errors at Pipeline End

```cure
# Good: Single error handling point
let result = data |> pipeline |> of |> operations
match result do
  Ok(value) -> handle_success(value)
  Error(e) -> handle_error(e)
end
```

### Do: Use with Result-Returning Functions

```cure
# Good: Natural error propagation
def process(input: String): Result(Output, Error) =
  input
  |> parse         # Returns Result
  |> validate      # Returns Result
  |> transform     # Returns Result
```

### Don't: Mix with Non-Result Returns Unnecessarily

```cure
# Inconsistent: mix of Result and non-Result
  input
  |> operation1    # Returns Int
  |> operation2    # Returns Result(Int, Error)
  |> operation3    # Returns Int

# Better: Consistent Result types
  input
  |> operation1_safe   # Returns Result(Int, Error)
  |> operation2        # Returns Result(Int, Error)
  |> operation3_safe   # Returns Result(Int, Error)
```

## Performance Considerations

The pipe operator has minimal overhead:

1. **Compile-time**: Parser precedence handling and AST construction
2. **Runtime**: One function call to `cure_std:pipe/2` per pipe operation
3. **Optimization**: The type optimizer can inline simple pipes in monomorphic code

For performance-critical paths where you know errors won't occur, consider direct function calls instead of piping.

## Comparison with Other Languages

### vs. Elixir `|>`

**Similarities**:
- Left-to-right data flow
- Lowest precedence
- Natural transformation pipelines

**Differences**:
- Cure's pipe has monadic semantics (automatic error handling)
- Elixir's pipe is purely syntactic (no error propagation)

### vs. Rust `?` Operator

**Similarities**:
- Automatic error propagation
- Short-circuit on error
- Result/Option type integration

**Differences**:
- Cure's pipe is an infix operator (readable left-to-right)
- Rust's `?` is a postfix operator (early return semantics)

### vs. Haskell `>>=` (Bind)

**Similarities**:
- Monadic composition
- Error propagation through Maybe/Either

**Differences**:
- Cure's pipe is operator-based (more accessible syntax)
- Haskell's bind is more general (works with any Monad)

## Advanced Topics

### Custom Monadic Types

The pipe operator currently works with Result types (`Ok`/`Error`). Future versions may support:
- Option types (`Some`/`None`)
- Custom monadic types through traits
- Async/await integration

### Type-Level Optimizations

The type checker and optimizer can:
- Eliminate redundant wrapping/unwrapping
- Inline monomorphic pipe chains
- Prove error-free pipelines and generate direct calls

### Debugging Pipelines

Use `let` bindings to inspect intermediate values:

```cure
def debug_pipeline(input: String): String =
  let step1 = input |> parse
  let step2 = step1 |> validate
  let step3 = step2 |> process
  step3
```

## See Also

- [Result Type Documentation](result_type.md)
- [Error Handling Guide](error_handling.md)
- [Function Composition](composition.md)
- [Type System Overview](type_system.md)
