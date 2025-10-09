# WARP.md

This file provides guidance to WARP (warp.dev) when working with code in this repository.

## Project Overview

Cure is a strongly-typed, dependently-typed programming language for the BEAM virtual machine with built-in finite state machines (FSMs) and actor model primitives. The project implements a complete compiler toolchain from lexical analysis through BEAM bytecode generation.

## Key Architecture Components

### Compiler Pipeline
The compiler follows a standard multi-stage pipeline:
1. **Lexer** (`src/lexer/`) - Tokenization with position tracking
2. **Parser** (`src/parser/`) - AST generation with recursive descent parsing
3. **Type System** (`src/types/`) - Dependent type checking and optimization
4. **FSM Runtime** (`src/fsm/`) - Finite state machine compilation and runtime
5. **Code Generation** (`src/codegen/`) - BEAM bytecode output

### Core Language Features
- **Dependent Types**: Types that can depend on values (e.g., `Vector(T, n: Nat)`)
- **Built-in FSMs**: First-class finite state machines with timeout and event handling
- **Actor Model**: Native BEAM process integration
- **Pattern Matching**: Advanced matching with dependent type constraints

### AST Structure
The AST is defined in `src/parser/cure_ast.hrl` with comprehensive record definitions for all language constructs including:
- Module definitions with exports
- Function definitions with dependent types
- FSM definitions with states and transitions
- Expression types (literals, function calls, pattern matching)
- Type expressions (primitive, dependent, function, union types)

## Common Development Commands

### Building
```bash
make all                 # Build complete compiler
make compiler           # Build compiler components only
make clean              # Remove build artifacts
```

### Testing
```bash
make test               # Run complete test suite
make shell              # Start Erlang shell with modules loaded

# Run individual test modules
erl -pa _build/ebin -s lexer_test run -s init stop
erl -pa _build/ebin -s parser_test run -s init stop
erl -pa _build/ebin -s fsm_test run -s init stop
```

### Development Workflow
```bash
make clean && make all && make test  # Full rebuild and test cycle
make shell                           # Interactive development
```

### Code Formatting (IMPORTANT - Erlang Project)
**This is an Erlang project - DO NOT use Elixir tools:**
- ❌ DO NOT run `mix format` or `mix credo`
- ✅ Use `rebar3 fmt` for code formatting
- ✅ Use `erlfmt` for Erlang source formatting

```bash
rebar3 fmt              # Format all Erlang source files
rebar3 fmt --check      # Check formatting without changes
```

## Testing Structure

Tests are organized by compiler component:
- `lexer_test.erl` - Token recognition and lexical analysis
- `parser_test.erl` - AST generation and syntax parsing  
- `types_test.erl` - Type system and dependent type checking
- `fsm_test.erl` - FSM compilation and runtime behavior
- `codegen_test.erl` - BEAM bytecode generation
- `*_performance_test.erl` - Performance and optimization tests

All tests follow the pattern of importing the module under test and using EUnit-style assertions.

## Key Implementation Patterns

### Error Handling
- Parser uses `{ok, Result}` | `{error, Reason}` pattern
- Position tracking in tokens for precise error reporting
- Graceful error recovery in parser with contextual messages

### Type System Architecture
The type optimizer (`src/types/cure_type_optimizer.erl`) implements several optimization phases:
- **Monomorphization**: Converting polymorphic functions to monomorphic versions
- **Function Specialization**: Creating specialized versions for frequent call patterns  
- **Inlining**: Inline small functions based on cost/benefit analysis
- **Dead Code Elimination**: Removing unused code paths

Configuration controlled via `#optimization_config{}` record in `cure_type_optimizer.hrl`.

### FSM Compilation
FSMs compile to BEAM gen_statem behaviors with:
- State definitions mapping to gen_statem states
- Event transitions as gen_statem callbacks
- Timeout handling integrated with BEAM's timeout mechanisms
- State data management for dependent FSM types

## File Organization Patterns

```
src/
├── lexer/cure_lexer.erl              # Tokenization engine
├── parser/
│   ├── cure_parser.erl               # Parser implementation  
│   ├── cure_ast.hrl                  # AST record definitions
│   └── cure_ast.erl                  # AST utility functions
├── types/
│   ├── cure_types.erl                # Type system core
│   ├── cure_typechecker.erl          # Type checking logic
│   └── cure_type_optimizer.erl       # Type-directed optimizations
├── fsm/
│   ├── cure_fsm_runtime.erl          # FSM runtime system
│   └── cure_fsm_builtins.erl         # Built-in FSM functions
└── codegen/
    ├── cure_codegen.erl              # Main codegen entry
    └── cure_beam_compiler.erl        # BEAM-specific compilation
```

## Language Examples Reference

See `examples/` directory for:
- `simple.cure` - Basic syntax and module definitions
- `fsm_demo.cure` - Comprehensive FSM examples with traffic lights and counters
- `dependent_types.cure` - Dependent type system demonstrations

## Build System Details

The Makefile supports:
- Automatic dependency tracking for Erlang files
- Incremental compilation with proper include paths
- Test execution with module loading
- Development shell with compiled modules pre-loaded
- Directory structure creation for build artifacts

Build artifacts go to `_build/ebin/` with subdirectory structure mirroring `src/`.

## Debugging and Development Tips

- Use `make shell` for interactive development
- FSM debugging available via `fsm_info/1` calls  
- Type system tracing can be enabled in optimization config
- BEAM disassembly available for generated code inspection
- Error messages include source position information for precise debugging