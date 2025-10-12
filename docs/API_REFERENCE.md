# Cure API Reference

## Overview

This document provides comprehensive API documentation for the Cure programming language - a strongly-typed, dependently-typed language for the BEAM virtual machine with built-in finite state machines (FSMs) and actor model primitives.

## Table of Contents

1. [Compiler API](#compiler-api)
2. [Standard Library](#standard-library)
3. [FSM Runtime API](#fsm-runtime-api)
4. [Type System API](#type-system-api)
5. [CLI Interface](#cli-interface)
6. [Build System Integration](#build-system-integration)
7. [Runtime System](#runtime-system)
8. [Integration Examples](#integration-examples)

## Compiler API

The Cure compiler provides a complete toolchain from lexical analysis through BEAM bytecode generation.

### Command Line Interface

#### `cure_cli:main/1`
```erlang
main(Args :: [string()]) -> no_return().
```
Main entry point for the Cure compiler CLI.

**Usage:**
```bash
cure input.cure                    # Compile with defaults
cure input.cure -o output.beam     # Specify output file
cure input.cure --verbose          # Verbose compilation
cure input.cure --no-optimize      # Disable optimizations

# Wrapper script special commands:
cure build                         # Execute 'make all'
cure test                          # Execute 'make test'
cure shell                         # Start development shell
cure clean                         # Execute 'make clean'
```

**Options:**
- `-o, --output FILE` - Output file path
- `-d, --output-dir DIR` - Output directory (default: `_build/ebin`)
- `--verbose` - Enable verbose output
- `--no-debug` - Disable debug information
- `--no-warnings` - Suppress warnings
- `--no-type-check` - Skip type checking
- `--no-optimize` - Disable optimizations
- `--help, -h` - Show help
- `--version, -v` - Show version

#### `cure_cli:compile_file/1,2`
```erlang
compile_file(Filename :: string()) -> {ok, OutputFile} | {error, Reason}.
compile_file(Filename :: string(), Options :: compile_options()) -> {ok, OutputFile} | {error, Reason}.
```
Programmatically compile a .cure file.

#### `cure_cli:add_automatic_stdlib_imports/2`
```erlang
add_automatic_stdlib_imports(Source :: string(), Options :: compile_options()) -> string().
```
Automatically add standard library imports to source code that lacks explicit imports.

#### `cure_cli:has_explicit_module_or_imports/1`
```erlang
has_explicit_module_or_imports(Source :: string()) -> boolean().
```
Check if source code contains explicit module definitions or imports.

#### `cure_cli:ensure_stdlib_available/1`
```erlang
ensure_stdlib_available(Options :: compile_options()) -> ok | {error, Reason}.
```
Ensure standard library is compiled and available, compiling if necessary.

#### `cure_cli:convert_beam_to_source_path/1`
```erlang
convert_beam_to_source_path(BeamPath :: string()) -> {ok, SourcePath} | error.
```
Convert BEAM file path to corresponding source file path.

### Lexical Analysis

#### `cure_lexer:tokenize/1`
```erlang
tokenize(Input :: binary()) -> {ok, [Token]} | {error, {Line, Column, Reason}}.
```
Tokenizes Cure source code into a list of tokens.

**Token Types:**
- `{identifier, Line, Name}` - Variable/function names
- `{keyword, Line, Keyword}` - Language keywords (def, fsm, match, etc.)
- `{operator, Line, Op}` - Operators (+, -, ->, |>, etc.)
- `{literal, Line, Value}` - Numeric, string, and boolean literals
- `{delimiter, Line, Delim}` - Parentheses, brackets, braces

**Example:**
```erlang
cure_lexer:tokenize(<<"def add(x, y) = x + y">>).
% Returns: {ok, [{keyword,1,def},{identifier,1,"add"},...]}
```

### Parsing

#### `cure_parser:parse/1`
```erlang
parse(Tokens :: [Token]) -> {ok, AST} | {error, {Line, Reason}}.
```
Parses tokens into an Abstract Syntax Tree (AST).

**AST Node Types:**
- `#function{}` - Function definitions
- `#fsm{}` - FSM definitions
- `#module{}` - Module definitions
- `#expression{}` - Expressions
- `#type{}` - Type expressions

**Example:**
```erlang
{ok, Tokens} = cure_lexer:tokenize(<<"def add(x, y) = x + y">>),
{ok, AST} = cure_parser:parse(Tokens).
```

#### `cure_parser:parse_file/1`
```erlang
parse_file(Filename :: string()) -> {ok, AST} | {error, Reason}.
```
Parse a Cure source file directly.

### Type System

#### `cure_typechecker:check_program/1`
```erlang
check_program(AST :: term()) -> {ok, TypedAST} | {error, [TypeError]}.
```
Type-check a program AST with dependent type support.

**Type Error Format:**
```erlang
{type_error, Line, {expected, ExpectedType, actual, ActualType}}.
{constraint_error, Line, {constraint, Constraint, reason, Reason}}.
{undefined_variable, Line, VarName}.
```

#### `cure_types:infer_type/2`
```erlang
infer_type(Expression :: term(), Context :: type_context()) -> {Type, [Constraint]}.
```
Infer the type of an expression with constraints.

#### `cure_type_optimizer:optimize/2`
```erlang
optimize(TypedAST :: term(), Options :: optimization_options()) -> OptimizedAST.
```
Apply type-directed optimizations:
- **Monomorphization** - Convert polymorphic functions to monomorphic versions
- **Function Specialization** - Create specialized versions for frequent patterns
- **Inlining** - Inline small functions based on cost/benefit analysis
- **Dead Code Elimination** - Remove unused code paths

### Code Generation

#### `cure_codegen:compile_program/1,2`
```erlang
compile_program(TypedAST :: term()) -> {ok, BeamBinary} | {error, Reason}.
compile_program(TypedAST :: term(), Options :: codegen_options()) -> {ok, BeamBinary} | {error, Reason}.
```
Compile a typed AST to BEAM bytecode.

**Code Generation Options:**
- `debug_info` - Include debug information (default: true)
- `optimize` - Enable optimizations (default: true)
- `fsm_runtime` - Include FSM runtime support (default: true)

#### `cure_beam_compiler:compile_to_beam/2`
```erlang
compile_to_beam(ErlangForms :: [abstract_form()], Options :: [term()]) -> binary().
```
Compile Erlang abstract forms to BEAM bytecode.

## Standard Library

The Cure standard library is implemented in Cure itself with Erlang runtime support.

### Core Types

#### Result Type
```cure
type Result(T, E) = Ok(T) | Error(E)
```
Used for error handling without exceptions.

**Functions:**
- `ok/1` - Create a successful result
- `error/1` - Create an error result
- `map_ok/2` - Transform successful value
- `and_then/2` - Chain operations that may fail
- `unwrap_or/2` - Get value or default

#### Option Type
```cure
type Option(T) = Some(T) | None
```
Used for nullable values.

**Functions:**
- `some/1` - Create a Some value
- `none/0` - Create None
- `map/2` - Transform contained value
- `filter/2` - Filter based on predicate
- `unwrap_or/2` - Get value or default

### List Operations

#### `Std.List` Module
```cure
# Core list functions
def length(list: List(T, n)): Int = n
def head(list: List(T, n)): T when n > 0
def tail(list: List(T, n)): List(T, n-1) when n > 0
def append(xs: List(T, n), ys: List(T, m)): List(T, n+m)

# Higher-order functions
def map(f: T -> U, list: List(T, n)): List(U, n)
def filter(pred: T -> Bool, list: List(T, n)): List(T, m) when m <= n
def fold_left(f: (Acc, T) -> Acc, acc: Acc, list: List(T)): Acc
def fold_right(f: (T, Acc) -> Acc, acc: Acc, list: List(T)): Acc

# Safe operations
def safe_head(list: List(T)): Option(T)
def safe_tail(list: List(T)): Option(List(T))
def safe_nth(list: List(T), index: Int): Option(T)
```

### Mathematical Functions

#### `Std.Math` Module
```cure
# Constants
val pi: Float = 3.141592653589793
val e: Float = 2.718281828459045

# Basic operations
def abs(x: Int): Nat
def abs(x: Float): Float when result >= 0.0
def min(x: T, y: T): T where T: Ord
def max(x: T, y: T): T where T: Ord

# Advanced functions
def sqrt(x: Float): Float when x >= 0.0
def power(base: Float, exp: Float): Float
def sin(x: Float): Float
def cos(x: Float): Float
def log(x: Float): Float when x > 0.0

# Safe operations
def safe_divide(x: Float, y: Float): Result(Float, String)
def safe_sqrt(x: Float): Result(Float, String)
```

## FSM Runtime API

The FSM runtime provides native support for finite state machines.

### FSM Lifecycle

#### `cure_fsm_runtime:spawn_fsm/1,2`
```erlang
spawn_fsm(Type :: atom()) -> pid().
spawn_fsm(Type :: atom(), InitData :: term()) -> pid().
```
Spawn a new FSM process.

#### `cure_fsm_runtime:stop_fsm/1`
```erlang
stop_fsm(FsmPid :: pid()) -> ok.
```
Gracefully stop an FSM process.

### FSM Communication

#### `cure_fsm_runtime:send_event/2,3`
```erlang
send_event(FsmPid :: pid(), Event :: term()) -> ok.
send_event(FsmPid :: pid(), Event :: term(), Timeout :: integer()) -> ok | timeout.
```
Send events to FSM processes.

#### `cure_fsm_runtime:get_state/1`
```erlang
get_state(FsmPid :: pid()) -> {StateName :: atom(), StateData :: term()}.
```
Get the current state of an FSM.

### FSM Inspection

#### `cure_fsm_runtime:get_fsm_info/1`
```erlang
get_fsm_info(FsmPid :: pid()) -> fsm_info().
```
Get detailed FSM information for debugging:
```erlang
-record(fsm_info, {
    type :: atom(),
    current_state :: atom(),
    state_data :: term(),
    transitions :: [transition()],
    message_queue :: [term()]
}).
```

### Built-in FSMs

#### Counter FSM
```cure
fsm Counter(initial: Int) do
  states: [Counting]
  initial: Counting
  data: {value: Int}

  state Counting do
    event(:increment) -> 
      data.value := data.value + 1
      Counting
    event(:decrement) when data.value > 0 -> 
      data.value := data.value - 1
      Counting
    event(:reset) ->
      data.value := initial
      Counting
  end
end
```

## Type System API

### Dependent Types

Cure supports dependent types where types can depend on values:

```cure
# Vector with compile-time known length
type Vector(T, n: Nat) = List(T, n)

# Safe array access
def get_element(vec: Vector(T, n), index: Nat): T when index < n =
  # Type system guarantees index is valid
  unsafe_get(vec, index)
```

### Type Constraints

```cure
# Constrained function parameters
def positive_sqrt(x: Float): Float when x > 0.0 =
  sqrt(x)

# Dependent return types
def replicate(n: Nat, value: T): List(T, n) =
  if n == 0 then []
  else [value | replicate(n-1, value)]
  end
```

### Type Classes

```cure
typeclass Ord(T) where
  def compare(x: T, y: T): Ordering
end

typeclass Show(T) where
  def show(x: T): String
end

# Automatic derivation
derive Show for List(T) when Show(T)
derive Ord for List(T) when Ord(T)
```

## CLI Interface

### Build Commands

```bash
# Basic compilation
make all                    # Build complete compiler and stdlib
make compiler               # Build compiler only
make stdlib                 # Build standard library
make test                   # Run test suite

# Development commands  
make shell                  # Start Erlang shell with modules
make clean                  # Clean build artifacts
make format                 # Format code with rebar3 fmt

# Testing
make test-basic             # Run basic tests
make test-integration       # Run integration tests
make test-performance       # Run performance tests
```

### File Compilation

```bash
# Compile single files
make compile-file CURE_FILE=examples/simple.cure
make compile-file CURE_FILE=lib/std.cure OUTPUT=custom.beam

# Direct compiler usage
./cure examples/simple.cure --verbose
./cure lib/std/math.cure -o math.beam --no-debug
```

## Build System Integration

### Makefile Integration

The build system provides comprehensive support for mixed Erlang/Cure projects:

```makefile
# Add to your Makefile
CURE_FILES = $(wildcard src/*.cure)
CURE_BEAM = $(patsubst src/%.cure,ebin/%.beam,$(CURE_FILES))

# Compilation rule
ebin/%.beam: src/%.cure
	cure "$<" -o "$@" --verbose

all: $(CURE_BEAM)
```

### Rebar3 Integration

```erlang
%% rebar.config
{pre_hooks, [
    {compile, "make -C deps/cure compiler"}
]}.

{plugins, [
    {cure_rebar_plugin, {git, "https://github.com/cure-lang/rebar3_cure", {branch, "main"}}}
]}.
```

## Runtime System

### BEAM Integration

Cure compiles to native BEAM bytecode and integrates seamlessly with Erlang/OTP:

```erlang
%% Calling Cure functions from Erlang
math_utils:factorial(5).     % Calls Cure function
list_utils:map(Fun, List).   % Calls Cure higher-order function

%% FSMs as OTP processes
{ok, Pid} = cure_fsm_runtime:spawn_fsm(traffic_light),
ok = cure_fsm_runtime:send_event(Pid, go).
```

### Performance Characteristics

- **Function calls**: ~10ns overhead for local calls
- **FSM events**: ~1μs including message passing
- **Type checking**: Zero runtime overhead (compile-time only)
- **Memory usage**: Similar to equivalent Erlang code
- **Garbage collection**: Uses BEAM's GC (per-process, generational)

### Error Handling

Cure integrates with BEAM's supervision trees and error handling:

```cure
def safe_operation(): Result(T, String) =
  try
    risky_operation()
  catch
    {error, Reason} -> Error(atom_to_string(Reason))
    {exit, Reason} -> Error("Process exited: " ++ atom_to_string(Reason))
  end
```

## Integration Examples

### Calling from Erlang

```erlang
%% Assuming compiled Cure modules
-module(example).
-export([test/0]).

test() ->
    % Call Cure standard library
    42 = 'Std.Math':abs(-42),
    [2,4,6] = 'Std.List':map(fun(X) -> X * 2 end, [1,2,3]),
    
    % Use Cure FSMs
    Counter = cure_fsm_runtime:spawn_fsm('Counter', 0),
    ok = cure_fsm_runtime:send_event(Counter, increment),
    {counting, 1} = cure_fsm_runtime:get_state(Counter).
```

### Calling from Elixir

```elixir
defmodule Example do
  def test do
    # Call Cure standard library
    42 = :"Std.Math".abs(-42)
    [2,4,6] = :"Std.List".map(&(&1 * 2), [1,2,3])
    
    # Use Cure FSMs
    {:ok, counter} = :cure_fsm_runtime.spawn_fsm(:"Counter", 0)
    :ok = :cure_fsm_runtime.send_event(counter, :increment)
    {:counting, 1} = :cure_fsm_runtime.get_state(counter)
  end
end
```

### OTP Supervision

```erlang
%% supervisor.erl
init([]) ->
    Children = [
        #{
            id => cure_fsm_supervisor,
            start => {cure_fsm_runtime, start_supervisor, []},
            type => supervisor
        }
    ],
    {ok, {#{strategy => one_for_all, intensity => 10, period => 10}, Children}}.
```

## Testing API

The Cure compiler includes comprehensive test suites for CLI wrapper functionality, standard library operations, and core compiler components.

### CLI Testing

#### `run_all_new_tests:run/0`
```erlang
run() -> ok | {error, {tests_failed, Count}}.
```
Execute all comprehensive CLI wrapper and standard library test suites.

#### `cli_wrapper_comprehensive_test:run/0`
```erlang
run() -> ok.
```
Run comprehensive CLI wrapper tests including:
- Cure wrapper script build command execution
- Missing BEAM modules detection and reporting
- Automatic stdlib import addition and detection
- Standard library compilation failure reporting
- Std.List.length function behavior and performance

### Component-Specific Testing

#### `cure_wrapper_script_test:run/0`
```erlang
run() -> ok.
```
Focused tests for wrapper script build command and error reporting.

#### `cure_cli_stdlib_imports_test:run/0`
```erlang
run() -> ok.
```
Tests for CLI automatic stdlib imports with comprehensive edge cases.

#### `stdlib_compilation_failure_test:run/0`
```erlang
run() -> ok.
```
Tests for stdlib compilation partial failure formatting and reporting.

#### `std_list_length_function_test:run/0`
```erlang
run() -> ok.
```
Comprehensive tests for Std.List.length function with various data types and performance benchmarks.

**Usage Examples:**
```bash
# Run all new comprehensive tests
erl -pa _build/ebin -pa test -s run_all_new_tests run -s init stop

# Run individual test suites
erl -pa _build/ebin -pa test -s cli_wrapper_comprehensive_test run -s init stop
erl -pa _build/ebin -pa test -s cure_wrapper_script_test run -s init stop
```

This API reference covers the complete Cure compiler and runtime system. For more detailed examples and language features, see the [Language Specification](LANGUAGE_SPEC.md) and [Feature Reference](FEATURE_REFERENCE.md).
