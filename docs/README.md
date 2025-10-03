# Cure Programming Language

A dependently-typed functional programming language targeting the BEAM virtual machine with built-in finite state machines and actor model primitives.

## Overview

Cure is a modern functional programming language that combines:
- **Dependent Types**: Type-level computation and refinement types for enhanced correctness
- **BEAM VM Target**: Compiles to efficient BEAM bytecode for compatibility with Erlang/Elixir ecosystem
- **Built-in FSMs**: Finite state machines as first-class language constructs
- **Actor Model**: Native support for concurrent, distributed programming

## Language Features

### Core Language
- Functional programming with immutable data structures
- Pattern matching and algebraic data types
- Type inference with optional type annotations
- Module system with imports and exports
- Let bindings and local scoping

### Dependent Types
```cure
# Refinement types for enhanced safety
def safe_head(list: List(T, n)) -> T when n > 0 = 
  match list do [x|_] -> x end

# Length-indexed lists
def concat(list1: List(T, n), list2: List(T, m)) -> List(T, n+m) = 
  list1 ++ list2
```

### Finite State Machines
```cure
fsm TrafficLight do
  states: [Red, Yellow, Green]
  initial: Red
  
  state Red do
    event(:next) -> Green
    timeout(5000) -> Green
  end
  
  state Green do
    event(:next) -> Yellow  
    timeout(3000) -> Yellow
  end
  
  state Yellow do
    event(:next) -> Red
    timeout(1000) -> Red
  end
end

# Using FSMs in functions
def demo() =
  let light = fsm_spawn(TrafficLight)
  fsm_send(light, :next)
  fsm_state(light)  # Returns: Green
```

### Actor Model Integration
```cure
def spawn_multiple_lights() =
  let lights = [
    fsm_spawn(TrafficLight),
    fsm_spawn(TrafficLight), 
    fsm_spawn(TrafficLight)
  ]
  
  # Coordinate multiple FSMs
  map(lights, fn(light) -> 
    fsm_send(light, :next)
    light
  end)
```

## Architecture

### Compilation Pipeline
```
Cure Source (.cure)
       ↓
   Lexer (tokens)
       ↓  
   Parser (AST)
       ↓
   Type Checker (typed AST)
       ↓
   Code Generator (BEAM bytecode)
       ↓
   BEAM VM Execution
```

### Project Structure
```
cure/
├── src/
│   ├── lexer/          # Tokenization
│   ├── parser/         # AST generation
│   ├── types/          # Dependent type system
│   ├── codegen/        # BEAM code generation
│   ├── fsm/            # FSM runtime system
│   └── runtime/        # Runtime integration
├── test/               # Test suites
├── examples/           # Example programs
├── docs/               # Documentation
└── _build/             # Build artifacts
```

## Build System

The project uses a custom Makefile for building:

```bash
# Build the complete compiler
make all

# Clean build artifacts
make clean

# Run test suites
make test

# Start development shell
make shell

# Generate documentation
make docs
```

## Components Status

### ✅ Completed Components

1. **Lexical Analysis** - Complete tokenizer with support for all language constructs
2. **Parser** - Recursive descent parser generating comprehensive AST
3. **Type System** - Dependent type checker with unification and constraint solving
4. **FSM Runtime** - Complete finite state machine implementation
5. **Code Generation** - BEAM bytecode generation from typed AST

### 🚧 In Progress

1. **FSM Compiler Integration** - Enhanced FSM-to-BEAM compilation
2. **Type-directed Optimizations** - Advanced optimizations using type information
3. **Runtime System** - Full BEAM VM integration features

### 📋 Planned

1. **Standard Library** - Core libraries and built-in functions  
2. **Development Tools** - REPL, debugger, package manager
3. **Documentation** - Language specification and tutorials
4. **Examples** - Comprehensive example programs

## Getting Started

### Prerequisites
- Erlang/OTP 24+ 
- Make
- Git

### Building
```bash
git clone <repository>
cd cure
make all
```

### Running Examples
```bash
# Parse and type-check an example
make shell
> cure_parser:parse_file("examples/simple.cure").
> cure_typechecker:check_program(AST).

# Compile to BEAM bytecode  
> cure_codegen:compile_program(AST).
```

### Running Tests
```bash
make test

# Or run individual test suites
cd _build/ebin
erl -pa . -s lexer_test run -s init stop
erl -pa . -s parser_test run -s init stop
erl -pa . -s types_test run -s init stop
erl -pa . -s fsm_test run -s init stop
erl -pa . -s codegen_test run -s init stop
```

## Documentation

- [Language Specification](language_spec.md) - Formal language definition
- [Type System](type_system.md) - Dependent type system documentation
- [FSM System](fsm_system.md) - Finite state machine primitives
- [Code Generation](code_generation.md) - BEAM compilation details
- [Development Progress](development_progress.md) - Implementation timeline
- [API Reference](api_reference.md) - Module and function documentation

## Examples

See the `examples/` directory for sample programs:
- `simple.cure` - Basic language features
- `comprehensive.cure` - Advanced constructs
- `fsm_demo.cure` - FSM usage examples
- `dependent_types.cure` - Type system features

## Contributing

This is a research/educational project. Contributions welcome!

## License

[Specify license here]

## Contact

[Contact information]