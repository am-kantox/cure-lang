%% Cure Programming Language - Standard Library Runtime
%% Provides core functions and types used by compiled Cure programs
-module(cure_std).

-moduledoc """
# Cure Programming Language - Standard Library Runtime

Provides core runtime functions that cannot be implemented in pure Cure due to
their need for Erlang-specific features. This module contains the essential
low-level operations for I/O, monadic operations, FSM integration, and
value serialization.

## Architecture

This module represents the boundary between pure Cure code and the underlying
Erlang runtime. Most standard library functions are now implemented in Cure
itself (in lib/std/), but this module contains the irreducible core that
requires direct Erlang integration.

### Core Responsibilities
- **Monadic Operations**: Implementation of Result/Option pipe semantics
- **I/O Operations**: Console output and formatting functions
- **FSM Integration**: Bridge to FSM runtime system
- **Value Serialization**: Converting Cure values to string representations
- **Runtime Utilities**: Low-level operations for runtime system

## Function Categories

### Monadic Operations
- `pipe/2` - Monadic pipe operator implementation
- `is_monad/1` - Type checking for Result/Option values

### I/O Functions
- `print/1` - Output without newline
- `println/1` - Output with newline
- `show/1` - Convert values to string representation

### FSM Operations
- `fsm_create/2` - Create FSM instances
- `fsm_send_safe/2` - Safe message sending to FSMs
- `create_counter/1` - Specialized counter FSM creation

### Utility Functions
- `list_to_string/1` - List serialization
- `join_ints/2` - Integer list formatting

## Monadic Pipe Semantics

The `pipe/2` function implements Cure's monadic pipe operator (|>) with
these rules:

1. **Error Propagation**: `Error(x) |> f` = `Error(x)`
2. **Ok Unwrapping**: `Ok(x) |> f` = `f(x)` (wrapped if not already monadic)
3. **Value Passing**: `x |> f` = `f(x)` (wrapped if not already monadic)

## Example Usage

```erlang
%% Direct function calls (typically from runtime)
cure_std:print("Hello, World!").
cure_std:pipe({'Ok', 5}, fun(X) -> X * 2 end).
%% Returns: {'Ok', 10}

cure_std:show({'Ok', [1, 2, 3]}).
%% Returns: "Ok([1, 2, 3])"
```

## Integration with Cure

Functions in this module are automatically registered in the runtime's
global function registry and can be called from Cure code using standard
function call syntax. The runtime handles the bridge between Cure's
type system and Erlang's dynamic typing.

## Error Handling

- I/O functions always succeed (return 'ok')
- Pipe operations catch Erlang exceptions and wrap them as Error values
- FSM operations return Result types for safe error handling
- Show function handles unknown types gracefully

## Performance Considerations

- All functions are designed for single-call efficiency
- String operations use efficient list concatenation
- Monadic operations minimize pattern matching overhead
- FSM operations are lightweight stubs (full implementation in cure_fsm_runtime)
""".

%% Core utility functions that cannot be implemented in Cure itself
%% (mainly Erlang interop and low-level runtime functions)
-export([
    % These remain in Erlang runtime as they need Erlang-specific features
    is_monad/1,
    wrap_ok/1,
    and_then/2,
    pipe/2,
    print/1,
    println/1,
    fsm_create/2,
    fsm_send_safe/2,
    create_counter/1,
    list_to_string/1,
    join_ints/2,
    show/1,
    % Nat type constructors
    'Zero'/0,
    'Succ'/1
]).

% NOTE: Most standard library functions are now implemented in Cure itself (lib/std/)
% This module only contains runtime functions that require Erlang-specific features

%% ============================================================================
%% Runtime Helper Functions
%% ============================================================================

-doc """
Checks if a value is a monadic type (Result or Option).

This function determines whether a value follows the monadic pattern
used by Cure's Result and Option types, which is essential for proper
pipe operator behavior.

## Arguments
- `Value` - Any Erlang term to check

## Returns
- `true` - Value is a Result (Ok/Error) type
- `false` - Value is not a monadic type

## Example
```erlang
cure_std:is_monad({'Ok', 42}).     %% true
cure_std:is_monad({'Error', msg}). %% true
cure_std:is_monad(42).             %% false
cure_std:is_monad([1, 2, 3]).      %% false
```

## Supported Monadic Types
- `{'Ok', Value}` - Successful result with value
- `{'Error', Reason}` - Failed result with error reason

Note: Option types (Some/None) are not currently detected as monadic
by this function, though they follow similar patterns.

## Usage
Primarily used internally by pipe/2 to determine whether function
results need to be wrapped in Ok constructors or can be returned as-is.
""".
is_monad({'Ok', _}) ->
    true;
is_monad({'Error', _}) ->
    true;
is_monad(_) ->
    false.

%% Wraps a value in the Ok Result constructor.
%% Used by the pipe operator to ensure values are properly typed as Results.
wrap_ok(Value) ->
    {'Ok', Value}.

%% Monadic bind operation (and_then)
%% and_then(Function, Result) applies Function to the value inside Ok,
%% or propagates Error unchanged.
%% Function signature: Fun :: (A -> Result(B, E)) takes unwrapped value.
and_then(Fun, {'Ok', Value}) when is_function(Fun, 1) ->
    try
        Fun(Value)
    catch
        Error:Reason -> {'Error', {and_then_runtime_error, Error, Reason}}
    end;
and_then(_Fun, {'Error', _} = Err) ->
    Err.

-doc """
Implements Cure's monadic pipe operator (|>) with Result type semantics.

This function is the core implementation of Cure's pipe operator, providing
monadic composition with automatic error propagation and value wrapping.
It handles three distinct cases based on the input value type.

## Arguments
- `LHO` - Left-hand operand (value to be piped)
- `RHO` - Right-hand operand (function to apply)

## Returns
- Result of applying RHO to LHO (possibly unwrapped), with appropriate wrapping
- Error values are propagated without calling RHO
- Runtime errors are caught and wrapped as Error values

## Pipe Rules

### Rule 1: Error Propagation
```erlang
cure_std:pipe({'Error', reason}, Fun).
%% Returns: {'Error', reason} (Fun is not called)
```

### Rule 2: Ok Unwrapping
```erlang
cure_std:pipe({'Ok', 5}, fun(X) -> X * 2 end).
%% Returns: {'Ok', 10} (value unwrapped, result wrapped)

cure_std:pipe({'Ok', 5}, fun(X) -> {'Ok', X * 2} end).
%% Returns: {'Ok', 10} (already monadic, not double-wrapped)
```

### Rule 3: Value Passing
```erlang
cure_std:pipe(5, fun(X) -> X * 2 end).
%% Returns: {'Ok', 10} (non-monadic input, result wrapped)

cure_std:pipe(5, fun(X) -> {'Error', 'too_big'} end).
%% Returns: {'Error', 'too_big'} (monadic result preserved)
```

## Error Handling
If RHO throws an exception during execution:
```erlang
cure_std:pipe({'Ok', 0}, fun(X) -> 1/X end).
%% Returns: {'Error', {pipe_runtime_error, error, badarith}}
```

## Usage in Cure
```cure
%% In Cure code, this becomes:
value |> function1 |> function2

%% Which compiles to:
pipe(pipe(value, function1), function2)
```

## Type Safety
The pipe operator maintains type safety by:
- Never double-wrapping already monadic values
- Propagating errors without execution
- Catching runtime exceptions as Error values
- Preserving monadic invariants through composition chains
""".
pipe({'Error', _} = Err, _RHO) ->
    % Rule 1: propagate error
    Err;
pipe({'Ok', V}, RHO) when is_function(RHO) ->
    % Rule 2: unwrap Ok(V), call RHO(V), wrap unless already a monad
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
    % Rule 3: pass non-monad LHO to RHO, wrap unless already a monad
    try
        Res = RHO(LHO),
        case is_monad(Res) of
            true -> Res;
            false -> {'Ok', Res}
        end
    catch
        Error:Reason -> {'Error', {pipe_runtime_error, Error, Reason}}
    end.

%% ============================================================================
%% IO Operations
%% ============================================================================

-doc """
Prints a message to standard output without adding a newline.

This function outputs text directly to the console using Erlang's I/O
formatting system. It's designed for inline output where you want to
continue writing on the same line.

## Arguments
- `Message` - String or list to print (must be printable)

## Returns
- `ok` - Always succeeds

## Example
```erlang
cure_std:print("Hello ").
cure_std:print("World!").
%% Output: "Hello World!"

cure_std:print("Count: ").
cure_std:print(integer_to_list(42)).
%% Output: "Count: 42"
```

## Usage in Cure
```cure
print("Processing...")
// Continue with other operations
print("Done!")
```

## Character Encoding
Supports Unicode text through Erlang's ~ts format specifier,
ensuring proper handling of international characters.

## Error Handling
I/O errors are handled by the underlying Erlang system.
This function always returns 'ok' from the Cure perspective.
""".
print(Message) ->
    cure_utils:debug("~ts", [Message]),
    ok.

-doc """
Prints a message to standard output followed by a newline.

This is the most commonly used output function, automatically adding
a newline character after the message for line-by-line output formatting.

## Arguments
- `Message` - String or list to print (must be printable)

## Returns
- `ok` - Always succeeds

## Example
```erlang
cure_std:println("First line").
cure_std:println("Second line").
%% Output:
%% First line
%% Second line

cure_std:println("Value: " ++ integer_to_list(42)).
%% Output: Value: 42
```

## Usage in Cure
```cure
println("Hello, World!")
println("This is on a new line")
```

## Character Encoding
Supports Unicode text through Erlang's ~ts format specifier,
ensuring proper handling of international characters.

## Comparison with print/1
- `print/1` - No newline, for inline output
- `println/1` - Adds newline, for line-based output

## Error Handling
I/O errors are handled by the underlying Erlang system.
This function always returns 'ok' from the Cure perspective.
""".
println(Message) ->
    cure_utils:debug("~ts~n", [Message]),
    ok.

%% ============================================================================
%% FSM Operations (Simplified Implementation)
%% ============================================================================

%% Create FSM (simplified)
fsm_create(_FSMType, _InitialState) ->
    % In a real implementation, this would create an actual FSM process
    {'Ok', make_ref()}.

%% Send message to FSM safely
fsm_send_safe(_FSMRef, _Message) ->
    % In a real implementation, this would send message to FSM process
    {'Ok', ok}.

%% Create counter FSM
create_counter(InitialValue) ->
    fsm_create(counter, InitialValue).

%% ============================================================================
%% Utility Functions
%% ============================================================================

%% Convert list of integers to string representation
list_to_string(List) ->
    "[" ++ join_ints(List, ", ") ++ "]".

%% Join integers with separator
join_ints([], _Sep) ->
    "";
join_ints([X], _Sep) ->
    integer_to_list(X);
join_ints([X | Rest], Sep) ->
    integer_to_list(X) ++ Sep ++ join_ints(Rest, Sep).

-doc """
Converts any Cure value to its string representation for debugging and display.

This function provides comprehensive string serialization for all Cure data
types, with special handling for monadic types (Result/Option) and structured
data like lists and tuples.

## Arguments
- `Value` - Any Cure/Erlang term to convert to string

## Returns
- String representation of the value
- "unknown" for unrecognized value types

## Examples

### Monadic Types
```erlang
cure_std:show({'Ok', 42}).        %% "Ok(42)"
cure_std:show({'Error', failed}). %% "Error(failed)"
cure_std:show({'Some', data}).    %% "Some(data)"
cure_std:show('None').            %% "None"
```

### Basic Types
```erlang
cure_std:show(42).           %% "42"
cure_std:show(3.14).         %% "3.14"
cure_std:show(hello).        %% "hello"
cure_std:show("string").     %% "string"
```

### Structured Types
```erlang
cure_std:show([1, 2, 3]).           %% "[1, 2, 3]"
cure_std:show({a, b}).              %% "{a, b}"
cure_std:show({1, 2, 3, 4}).        %% "{1, 2, 3, 4}"
cure_std:show({1, 2, 3, 4, 5}).     %% "{1, 2, 3, 4, ...}"
```

### Nested Structures
```erlang
cure_std:show({'Ok', [1, 2, {'Some', 3}]}).
%% "Ok([1, 2, Some(3)])"
```

## Usage in Cure
```cure
let value = Ok([1, 2, 3])
println(show(value))  // Outputs: Ok([1, 2, 3])
```

## Tuple Handling
- Tuples with 0-4 elements: Full representation
- Tuples with 5+ elements: Truncated with "..." suffix
- Nested tuples are recursively formatted

## Error Handling
Unknown or unsupported types return "unknown" rather than crashing,
making this function safe for debugging any Cure value.

## Performance Notes
- Recursive formatting for nested structures
- String concatenation using Erlang's efficient list operations
- Optimized for readability over performance
""".
show({'Ok', Value}) ->
    "Ok(" ++ show(Value) ++ ")";
show({'Error', Reason}) ->
    "Error(" ++ show(Reason) ++ ")";
show({'Some', Value}) ->
    "Some(" ++ show(Value) ++ ")";
show('None') ->
    "None";
show(Value) when is_atom(Value) ->
    atom_to_list(Value);
show(Value) when is_integer(Value) ->
    integer_to_list(Value);
show(Value) when is_float(Value) ->
    float_to_list(Value);
show(Value) when is_list(Value) ->
    "[" ++ string:join([show(Item) || Item <- Value], ", ") ++ "]";
show(Value) when is_tuple(Value) ->
    case tuple_size(Value) of
        0 ->
            "{}";
        1 ->
            "{" ++ show(element(1, Value)) ++ "}";
        2 ->
            "{" ++ show(element(1, Value)) ++ ", " ++ show(element(2, Value)) ++ "}";
        3 ->
            "{" ++ show(element(1, Value)) ++ ", " ++ show(element(2, Value)) ++ ", " ++
                show(element(3, Value)) ++ "}";
        4 ->
            "{" ++ show(element(1, Value)) ++ ", " ++ show(element(2, Value)) ++ ", " ++
                show(element(3, Value)) ++ ", " ++ show(element(4, Value)) ++ "}";
        _ ->
            "{" ++ show(element(1, Value)) ++ ", " ++ show(element(2, Value)) ++ ", " ++
                show(element(3, Value)) ++ ", " ++ show(element(4, Value)) ++ ", ...}"
    end;
show(_Value) ->
    "unknown".

%% ============================================================================
%% Nat Type Constructors
%% ============================================================================

-doc """
Nat type nullary constructor representing zero.

In Cure's Peano encoding of natural numbers:
- Zero represents 0
- Succ(Zero) represents 1
- Succ(Succ(Zero)) represents 2, etc.

## Returns
- 0 (represented as integer for runtime efficiency)

## Example
```erlang
cure_std:'Zero'().  %% Returns: 0
```

## Usage in Cure
```cure
def length(list: List(T)): Nat =
  match list do
    [] -> Zero
    [_ | t] -> Succ(length(t))
  end
```

## Type
- Zero : Nat
""".
'Zero'() ->
    0.

-doc """
Nat type unary constructor representing successor.

Takes a natural number and returns its successor (n+1).
This is the inductive case of Peano-encoded natural numbers.

## Arguments
- `N` - A natural number (Nat)

## Returns
- N+1 (next natural number)

## Example
```erlang
cure_std:'Succ'(0).        %% Returns: 1 (successor of Zero)
cure_std:'Succ'(5).        %% Returns: 6 (successor of 5)
```

## Usage in Cure
```cure
let one = Succ(Zero)
let two = Succ(Succ(Zero))
let three = Succ(two)
```

## Type
- Succ : Nat -> Nat
""".
'Succ'(N) when is_integer(N), N >= 0 ->
    N + 1.
