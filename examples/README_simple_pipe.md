# Simple Pipe Operator Example

This example demonstrates the basic usage of Cure's pipe operator (`|>`).

## File

`simple_pipe.cure` - A working example showcasing pipe operator functionality

## Compilation Status

✅ **Successfully compiles** through all stages:
- ✓ Lexical analysis
- ✓ Parsing  
- ✓ Type checking
- ✓ Code generation

## What It Demonstrates

### 1. Basic Pipe Chain
```cure
def demo() -> Result(Int, String) = 5 |> double |> increment
```
Chains simple transformations: 5 → 10 → 11, wrapped in Result type.

### 2. Multi-Step Pipeline
```cure
def chain_example() -> Result(Int, String) = 
  10 |> double |> add_five |> square
```
Longer chain: 10 → 20 → 25 → 625

### 3. Pipe with Arguments
```cure
def with_args() -> Result(Int, String) = 
  10 |> add(5) |> multiply(3)
```
The piped value becomes the first argument: add(10, 5) → multiply(15, 3) → 45

## Key Features

1. **Automatic Result Wrapping**: The pipe operator automatically wraps results in `Result(T, E)` type for error handling

2. **Monadic Semantics**: Pipes have built-in error propagation - if any step fails, the chain stops

3. **Type Safety**: Full type inference and checking ensures type correctness at compile time

## How to Test

### Compilation Test
```bash
cd /opt/Proyectos/Ammotion/cure

# Full compiler test
make clean && make all

# Compile the example
./cure examples/simple_pipe.cure
```

### Manual Testing
```erlang
% From Erlang shell
cd("/opt/Proyectos/Ammotion/cure").
code:add_pathz("_build/ebin").

% Parse
{ok, AST} = cure_parser:parse_file("examples/simple_pipe.cure").

% Type check
Result = cure_typechecker:check_program(AST).

% Code generate
{ok, Module} = cure_codegen:compile_module(hd(AST)).
```

## Expected Behavior

When executed, the functions should return:
- `demo()` → `Ok(11)`
- `chain_example()` → `Ok(625)`  
- `with_args()` → `Ok(45)`

All wrapped in Cure's Result type for safe error handling.

## Technical Notes

### Type Inference

The pipe operator has these type rules:
1. If left side is `Result(T)`, unwrap to get `T`
2. Pass `T` to the function on the right side
3. If function returns plain type `U`, wrap as `Result(U, E)`
4. If function already returns `Result`, use it as-is

This prevents double-wrapping Result types in chains.

### Return Type Declaration

Functions using pipe must declare Result return type:
```cure
def my_func() -> Result(Int, String) = value |> transform
```

This is because the pipe operator automatically wraps for error handling.

## See Also

- [Pipe Operator Documentation](../docs/pipe_operator.md)
- [Full Pipe Demo](pipe_demo.cure) - More comprehensive examples
- [Test Suite](../test/pipe_operator_test.erl) - Unit tests for all functionality
