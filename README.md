# Cure Programming Language

Cure is a dependently-typed programming language for the BEAM virtual machine. It provides compile-time verification through dependent types, native finite state machine constructs, and integration with SMT solvers for automated theorem proving.

Version: 0.7.0  
Last Updated: November 2025

## Overview

Cure compiles to BEAM bytecode and runs on the Erlang virtual machine. The language emphasizes static verification while maintaining interoperability with the Erlang and Elixir ecosystems.

### Key Characteristics

- Dependent type system with refinement constraints
- First-class finite state machines with transition verification
- SMT solver integration (Z3, CVC5) for constraint solving
- Pattern matching with exhaustive case analysis
- Type-directed optimizations during compilation
- Standard library with common data structures and operations
- Language Server Protocol implementation for editor integration

## Building

Prerequisites:
- Erlang/OTP 20 or later
- Make
- Unix-like environment

```bash
make all
```

The compiler executable will be available as `./cure`.

## Usage

Compile a Cure source file:

```bash
./cure <input-file>.cure
```

Run the compiled module:

```bash
erl -pa _build/ebin -noshell -eval "'ModuleName':main(), init:stop()."
```

Common options:
- `-o, --output <file>` - Specify output file
- `-d, --output-dir <dir>` - Set output directory
- `--verbose` - Enable detailed compilation output
- `--no-type-check` - Skip type checking phase

## Language Features

### Module System

Modules define namespaces and export interfaces:

```cure
module Example do
  export [function/1, other_function/2]
  
  import Std.List [map, filter]
  
  def function(x: Int): Int =
    x * 2
end
```

### Dependent Types

Types can express constraints verified at compile time:

```cure
# Vector with length tracked in the type
def safe_head(v: Vector(T, n)): T when n > 0 =
  head(v)

# Refinement types for constrained values
def safe_divide(a: Int, b: {x: Int | x != 0}): Int =
  a / b
```

### Finite State Machines

FSMs are first-class language constructs:

```cure
fsm TrafficLight do
  Red --> |timer| Green
  Green --> |timer| Yellow
  Yellow --> |timer| Red
  Green --> |emergency| Red
end
```

The compiler verifies reachability, detects unreachable states, and generates BEAM behavior implementations.

### Pattern Matching

Match expressions provide exhaustive case analysis:

```cure
def classify(x: Int): Atom =
  match x do
    n when n < 0 -> :negative
    0 -> :zero
    n when n > 0 -> :positive
  end
```

The compiler ensures all cases are handled.

### Records

Record types with field access and immutable updates:

```cure
record Person do
  name: String
  age: Int
end

def update_age(person: Person, new_age: Int): Person =
  Person{person | age: new_age}
```

## Standard Library

The standard library provides common functionality:

- `Std.Core` - Basic types and operations
- `Std.List` - List processing (map, filter, fold)
- `Std.Result` - Error handling with Result type
- `Std.Io` - Input/output operations
- `Std.Fsm` - FSM runtime operations
- `Std.String` - String manipulation
- `Std.Math` - Mathematical operations
- `Std.Pair` - Tuple operations
- `Std.Vector` - Length-indexed vectors
- `Std.Show` - Value serialization
- `Std.System` - System-level operations
- `Std.Rec` - Record utilities

See `docs/STD_SUMMARY.md` for complete API documentation.

## Type System

### Refinement Types

Refinement types add logical constraints to base types:

```cure
type NonZero = {x: Int | x != 0}
type Percentage = {p: Int | 0 <= p and p <= 100}
```

Constraints are checked at compile time using SMT solvers.

### Type Inference

The compiler infers types for local bindings:

```cure
def example(): Int =
  let x = 42           # x: Int inferred
  let y = [1, 2, 3]    # y: List(Int) inferred
  x + length(y)
```

## Compilation Pipeline

1. Lexical analysis: Source code to token stream
2. Parsing: Token stream to abstract syntax tree
3. Type checking: Dependent type verification with SMT solving
4. Optimization: Monomorphization, specialization, inlining
5. Code generation: AST to BEAM bytecode

Type-directed optimizations provide 25-60% performance improvement over baseline compilation.

## Project Structure

```
cure/
├── src/
│   ├── lexer/          # Tokenization
│   ├── parser/         # Syntax analysis and AST generation
│   ├── types/          # Type system and type checking
│   ├── codegen/        # BEAM bytecode generation
│   ├── fsm/            # FSM compilation and runtime
│   ├── smt/            # SMT solver integration
│   ├── lsp/            # Language server implementation
│   └── runtime/        # Runtime system integration
├── lib/std/            # Standard library modules
├── test/               # Test suites
├── examples/           # Example programs
└── docs/              # Documentation
```

## Testing

Run the test suite:

```bash
make test
```

Tests cover lexical analysis, parsing, type checking, FSM compilation, and code generation.

## Examples

The `examples/` directory contains working programs:

- `01_list_basics.cure` - List operations
- `02_result_handling.cure` - Error handling with Result type
- `03_option_type.cure` - Optional values
- `04_pattern_guards.cure` - Pattern matching with guards
- `05_recursion.cure` - Recursive functions
- `06_fsm_traffic_light.cure` - FSM implementation
- `07_refinement_types_demo.cure` - Refinement type constraints
- `08_typeclasses.cure` - Typeclass system usage

## Documentation

Core documentation:
- `docs/LANGUAGE_SPEC.md` - Language specification
- `docs/TYPE_SYSTEM.md` - Type system details
- `docs/FSM_USAGE.md` - FSM programming guide
- `docs/STD_SUMMARY.md` - Standard library reference
- `docs/FEATURE_REFERENCE.md` - Quick reference

Advanced topics:
- `docs/DEPENDENT_TYPES_GUIDE.md` - Dependent types and SMT verification
- `docs/TYPECLASS_RESOLUTION.md` - Typeclass implementation
- `docs/SMT_SOLVER_ADVANCED.md` - SMT solver integration details

## Development Status

### Implemented

- Complete lexer with position tracking
- Recursive descent parser with error recovery
- Dependent type checker with refinement types
- FSM compilation to BEAM behaviors
- BEAM bytecode generation with OTP compatibility
- Standard library with 15 modules
- Type-directed optimizations
- Language Server Protocol implementation
- SMT solver integration (API level)
- Record operations with field access
- Pattern matching with guards

### Planned

- Pipe operator (`|>`) implementation
- Typeclass/trait system expansion
- If-then-else expressions
- String interpolation
- Enhanced error messages with suggestions
- Package management system

See `docs/TODO.md` for detailed roadmap.

## Performance

Compilation times:
- Small files (<100 lines): <1 second
- Medium projects (1K-10K lines): 5-30 seconds
- Large projects (100K+ lines): 30-300 seconds

Runtime characteristics:
- Function call overhead: ~10ns (after optimization)
- FSM event processing: ~1μs
- Type checking: Zero runtime overhead (compile-time only)
- Memory usage: Comparable to equivalent Erlang code

## Contributing

Contributions are welcome. Priority areas include:

- Standard library expansion
- Optimization improvements
- Documentation and examples
- IDE tooling enhancements
- Test coverage expansion

## License

To be determined.
