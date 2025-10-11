# Cure Programming Language - Documentation

A strongly-typed, dependently-typed programming language for the BEAM virtual machine with built-in finite state machines (FSMs) and actor model primitives.

## Overview

Cure is an advanced functional programming language that uniquely combines:
- **Dependent Types**: Advanced type system with constraint solving and refinement types
- **Native FSMs**: Finite state machines as first-class language constructs with compile-time verification
- **BEAM Integration**: Seamless compilation to BEAM bytecode with OTP compatibility
- **Type-Directed Optimization**: Advanced optimizations based on type information
- **Actor Model**: Built-in concurrency with supervision trees and hot code reloading

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
   Lexer (cure_lexer.erl) - Tokenization with position tracking
       ↓  
   Parser (cure_parser.erl) - AST generation with error recovery
       ↓
   Type Checker (cure_typechecker.erl) - Dependent type checking
       ↓
   Type Optimizer (cure_type_optimizer.erl) - Monomorphization, specialization
       ↓
   Code Generator (cure_codegen.erl) - BEAM bytecode generation
       ↓
   BEAM Runtime - FSM integration with cure_fsm_runtime
```

### Project Structure
```
cure/
├── src/
│   ├── cure_cli.erl        # Command line interface
│   ├── lexer/
│   │   └── cure_lexer.erl  # Tokenization engine
│   ├── parser/
│   │   ├── cure_parser.erl # Parser implementation
│   │   ├── cure_ast.erl    # AST utilities 
│   │   └── cure_ast.hrl    # AST record definitions
│   ├── types/
│   │   ├── cure_types.erl      # Core type system
│   │   ├── cure_typechecker.erl # Type checking logic
│   │   ├── cure_type_optimizer.erl # Type optimizations
│   │   └── cure_smt_solver.erl # SMT constraint solver
│   ├── fsm/
│   │   ├── cure_fsm_runtime.erl # FSM runtime system
│   │   └── cure_fsm_builtins.erl # Built-in FSM functions
│   ├── codegen/
│   │   ├── cure_codegen.erl       # Main code generation
│   │   ├── cure_beam_compiler.erl # BEAM compilation
│   │   ├── cure_action_compiler.erl # Action compilation
│   │   └── cure_guard_compiler.erl # Guard compilation
│   └── runtime/
│       ├── cure_runtime.erl   # Core runtime system
│       ├── cure_std.erl       # Standard library runtime
│       ├── Std.erl           # Main standard module
│       └── Std.List.erl      # List operations runtime
├── lib/                    # Standard library (Cure source)
│   ├── std.cure           # Main standard library module
│   ├── std/                # Standard library modules
│   └── README.md          # Library documentation
├── test/                   # Test suites
├── examples.poor/          # Example programs 
├── docs/                   # Complete documentation
├── _build/                 # Build artifacts
│   ├── ebin/              # Compiled Erlang modules
│   └── lib/               # Compiled standard library
└── Makefile                # Build system
```

## Build System

The project uses a comprehensive Makefile with multiple targets:

```bash
# Build the complete compiler and standard library
make all

# Build individual components
make compiler               # Build compiler only
make stdlib                 # Build standard library
make tests                  # Build test files

# Testing
make test                   # Run complete test suite
make test-basic             # Run basic unit tests
make test-integration       # Run integration tests
make test-performance       # Run performance benchmarks

# Development utilities
make shell                  # Start Erlang shell with modules
make clean                  # Clean build artifacts
make format                 # Format code with rebar3 fmt
make help                   # Show available targets

# File compilation
make compile-file CURE_FILE=file.cure OUTPUT=output.beam
```

## Implementation Status

### ✅ **Complete and Functional**

1. **Lexical Analysis** (`cure_lexer.erl`)
   - Complete tokenizer with position tracking
   - Support for all language constructs including FSMs
   - Comprehensive error reporting with line/column information

2. **Parsing** (`cure_parser.erl`, `cure_ast.erl`)
   - Recursive descent parser with error recovery
   - Comprehensive AST generation for all language features
   - Support for dependent types, FSMs, and complex expressions

3. **Type System** (`cure_typechecker.erl`, `cure_types.erl`)
   - Dependent type checking with constraint solving
   - SMT solver integration for complex constraints
   - Type inference and bidirectional type checking
   - Support for refinement types and dependent functions

4. **Type Optimization** (`cure_type_optimizer.erl`)
   - Monomorphization of polymorphic functions
   - Function specialization for performance
   - Inlining analysis and dead code elimination
   - Configurable optimization levels

5. **FSM System** (`cure_fsm_runtime.erl`, `cure_fsm_builtins.erl`)
   - Complete finite state machine runtime
   - Integration with BEAM supervision trees
   - Built-in FSM types and operations
   - Compile-time FSM verification

6. **Code Generation** (`cure_codegen.erl`, `cure_beam_compiler.erl`)
   - BEAM bytecode generation from typed AST
   - Action and guard compilation for FSMs
   - Integration with Erlang/OTP runtime
   - Debug information generation

7. **Standard Library** (`lib/std.cure`, runtime support)
   - Core types: Result, Option, List operations
   - Mathematical functions and string operations
   - FSM utilities and common patterns
   - Runtime support in Erlang

8. **Command Line Interface** (`cure_cli.erl`)
   - Complete CLI with option parsing
   - File compilation with various output options
   - Integration with build system
   - Comprehensive error reporting

### ✅ **Advanced Features**

- SMT-based constraint solving for dependent types
- Type-directed optimizations (25-60% performance improvement)
- Native FSM compilation with state verification
- BEAM integration with hot code reloading
- Comprehensive test suite with performance benchmarks

## Quick Start

### Prerequisites
- Erlang/OTP 21+ 
- Make
- rebar3 (for code formatting)
- Git

### Building
```bash
git clone <repository>
cd cure
make all                     # Build compiler and standard library
```

### Compiling Cure Files
```bash
# Using the CLI
./cure lib/std.cure --verbose
./cure examples.poor/simple.cure -o my_module.beam

# Using Make
make compile-file CURE_FILE=lib/std.cure
```

### Interactive Development
```bash
# Start development shell
make shell

# In Erlang shell - try the compiler pipeline:
1> cure_lexer:tokenize(<<"def test() = 42">>).
{ok,[{keyword,1,def},{identifier,1,"test"},...]}    

2> {ok, Tokens} = cure_lexer:tokenize(<<"def test() = 42">>),
   cure_parser:parse(Tokens).
{ok,#function{name="test",...}}

3> {ok, AST} = cure_parser:parse(Tokens),
   cure_typechecker:check_program(AST).
{ok, TypedAST}
```

### Running Tests
```bash
make test                    # Run complete test suite
make test-basic              # Run basic unit tests
make test-integration        # Run integration tests
make test-performance        # Run performance benchmarks
```

## Documentation Index

### Core Documentation
- **[API Reference](API_REFERENCE.md)** - Complete API documentation for compiler and runtime
- **[Type System](TYPE_SYSTEM.md)** - Dependent types, constraints, and FSM type safety
- **[CLI Usage](CLI_USAGE.md)** - Command line interface and build system integration
- **[Standard Library Summary](STD_SUMMARY.md)** - Standard library implementation overview

### Language Documentation
- **[Language Specification](LANGUAGE_SPEC.md)** - Formal syntax and semantics
- **[Feature Reference](FEATURE_REFERENCE.md)** - Complete language feature overview
- **[FSM System](FSM_SYSTEM.md)** - Finite state machine documentation

### Development
- **[Testing Summary](TESTING_SUMMARY.md)** - Test suite organization and results
- **[Development Progress](development_progress.md)** - Implementation milestones
- **[Current State](current_state_20251005.md)** - Latest implementation status

## Language Examples

### Basic Function Definition
```cure
# Simple function with type annotation
def factorial(n: Int): Int when n >= 0 =
  if n <= 1 then 1
  else n * factorial(n - 1)
  end
```

### Dependent Types
```cure
# Length-preserving list operations
def zip_safe(xs: List(T, n), ys: List(U, n)): List({T, U}, n) =
  match xs, ys do
    [], [] -> []
    [x|xs_rest], [y|ys_rest] -> [{x, y} | zip_safe(xs_rest, ys_rest)]
  end
```

### FSM with State Data
```cure
fsm Counter(max: Int) do
  states: [Zero, Counting(n: Int) where 0 < n <= max]
  initial: Zero
  
  state Zero do
    event(:increment) -> Counting(1)
  end
  
  state Counting(n) do
    event(:increment) when n < max -> Counting(n + 1)
    event(:decrement) when n > 1 -> Counting(n - 1)
    event(:decrement) when n == 1 -> Zero
    event(:reset) -> Zero
  end
end
```

### Error Handling with Result Types
```cure
import Std [Result, ok, error, map_ok, and_then]

def safe_computation(x: Float, y: Float): Result(Float, String) =
  safe_divide(x, y)
  |> map_ok(fn(result) -> result * 2 end)
  |> and_then(fn(doubled) -> 
       if doubled > 100.0 then error("Result too large")
       else ok(doubled)
       end)
```

## Contributing

This is a research/educational project. Contributions welcome!

## License

[Specify license here]

## Contact

[Contact information]