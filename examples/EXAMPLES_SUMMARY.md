# Cure Language Examples - Complete Summary

## Created Files (15 examples + 1 README)

### 01_basics/ - Fundamental Language Syntax
1. **literals.cure** (74 lines) - All literal types
2. **functions.cure** (70 lines) - Functions, recursion, let bindings
3. **operators.cure** (77 lines) - Arithmetic, comparison, logical operators

### 02_types/ - Advanced Type System
4. **polymorphic.cure** (107 lines) - Generic functions and parametric polymorphism
5. **dependent.cure** (124 lines) - Dependent types, vectors, Peano numbers

### 03_patterns/ - Pattern Matching
6. **matching.cure** (173 lines) - Comprehensive pattern matching with guards

### 04_lists/ - List Operations (Std.List)
7. **list_operations.cure** (159 lines) - Complete Std.List API examples

### 05_vectors/ - Dependent Type Vectors
8. **vector_operations.cure** (136 lines) - Length-indexed vector operations

### 06_result_option/ - Error Handling
9. **error_handling.cure** (193 lines) - Result and Option types, monadic operations

### 07_fsm/ - Finite State Machines
10. **counter.cure** (85 lines) - Counter, bounded counter, up-down counter, timer
11. **traffic_light.cure** (101 lines) - Traffic lights with timing and sensors

### 08_higher_order/ - Functional Programming
12. **lambdas.cure** (170 lines) - Lambdas, composition, currying, pipelines

### 09_records/ - Structured Data
13. **records.cure** (199 lines) - Records with field access and updates

### 11_io/ - Input/Output
14. **io_examples.cure** (146 lines) - Console I/O with Std.Io

### 12_math/ - Mathematical Operations
15. **math_operations.cure** (185 lines) - Complete Std.Math API examples

### Documentation
16. **README.md** (247 lines) - Comprehensive guide to all examples

## Total Statistics
- **Total Examples**: 15 Cure files
- **Total Lines**: ~2,000+ lines of example code
- **Categories**: 12 different feature categories
- **Standard Libraries Covered**: List, Vector, Result, Core, Fsm, Io, Math

## Features Demonstrated

### Core Language Features
✓ Literals (integers, booleans, atoms, strings, lists, tuples)
✓ Functions and recursion
✓ Let bindings and pattern matching
✓ Operators (arithmetic, comparison, logical)
✓ Type annotations and type inference

### Advanced Type System
✓ Parametric polymorphism (generics)
✓ Dependent types (length-indexed vectors)
✓ Type-level arithmetic
✓ Peano natural numbers
✓ Type constraints

### Pattern Matching
✓ Basic patterns (literals, wildcards, variables)
✓ List destructuring and cons patterns
✓ Tuple patterns
✓ Guards with complex conditions
✓ Nested patterns
✓ Record patterns

### Standard Library
✓ Std.List - Complete API (map, filter, fold, zip_with, etc.)
✓ Std.Vector - Dependent type operations
✓ Std.Core - Core utilities
✓ Std.Result - Error handling
✓ Std.Fsm - State machines
✓ Std.Io - Console I/O
✓ Std.Math - Mathematical functions

### Functional Programming
✓ Higher-order functions
✓ Lambda expressions
✓ Function composition
✓ Currying and partial application
✓ Map, filter, fold patterns

### Data Structures
✓ Lists with pattern matching
✓ Tuples with destructuring
✓ Records with field access
✓ Generic records
✓ Nested structures

### State Management
✓ Finite State Machines (FSM)
✓ State transitions with events
✓ Guards on transitions
✓ Stateful data in FSMs
✓ Multiple FSM examples (counter, traffic light, timer)

### Error Handling
✓ Option type for optional values
✓ Result type for success/failure
✓ Safe operations returning Option/Result
✓ Monadic operations (map, flatMap)
✓ Chaining operations
✓ Validation pipelines

## Coverage of Cure AST Features

Based on src/parser/cure_ast.hrl:

✓ Module definitions with exports
✓ Function definitions with parameters and return types
✓ Type parameters for polymorphic functions
✓ Pattern matching (match expressions)
✓ Let bindings
✓ Binary and unary operators
✓ List and tuple expressions
✓ Record definitions and expressions
✓ FSM definitions with states and transitions
✓ Lambda expressions
✓ Function calls
✓ Literals (int, bool, atom, string)
✓ Import statements

## Ready for Testing

All examples:
- Have a main/0 function for easy execution
- Include comprehensive comments
- Demonstrate best practices
- Cover edge cases
- Are designed to compile successfully

## Next Steps

To verify all examples work:
1. Build the compiler: `make all`
2. Test each example directory
3. Run examples through the compiler
4. Verify compilation succeeds

Example test command:
```bash
for file in examples/*/*.cure; do
    echo "Testing $file"
    ./cure compile "$file" || echo "FAILED: $file"
done
```
