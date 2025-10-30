# Cure Programming Language - Examples

This directory contains comprehensive examples demonstrating all major features of the Cure programming language.

## Directory Structure

```
examples/
├── 01_basics/          - Basic syntax, literals, functions, operators
├── 02_types/           - Type system: polymorphic and dependent types
├── 03_patterns/        - Pattern matching with guards and destructuring
├── 04_lists/           - List operations using Std.List
├── 05_vectors/         - Length-indexed vectors with dependent types
├── 06_result_option/   - Error handling with Result and Option types
├── 07_fsm/             - Finite State Machines: counter, traffic light
├── 08_higher_order/    - Lambdas, composition, currying
├── 09_records/         - Record definitions, access, and updates
├── 10_traits/          - Trait system (when implemented)
├── 11_io/              - Console I/O with Std.Io
└── 12_math/            - Math operations with Std.Math
```

## Examples by Category

### 01_basics/ - Fundamental Syntax
- **literals.cure**: All literal types (integers, booleans, atoms, strings, lists, tuples)
- **functions.cure**: Function definitions, parameters, recursion, let bindings
- **operators.cure**: Arithmetic, comparison, and logical operators

### 02_types/ - Type System
- **polymorphic.cure**: Parametric polymorphism (generics)
  - Generic functions: identity, map, filter, fold
  - Type parameters and constraints
- **dependent.cure**: Dependent types
  - Length-indexed vectors
  - Peano natural numbers (Nat)
  - Type-level arithmetic

### 03_patterns/ - Pattern Matching
- **matching.cure**: Comprehensive pattern matching
  - Basic patterns on integers, booleans, atoms
  - List destructuring and cons patterns
  - Tuple patterns
  - Guards with complex conditions
  - Nested patterns
  - Option and Result pattern matching

### 04_lists/ - List Operations
- **list_operations.cure**: Using Std.List standard library
  - Basic operations: length, head, tail, reverse
  - Construction: cons, append, concat
  - Transformations: map, filter, fold, zip_with
  - Predicates: contains, is_empty
  - Complex pipelines combining operations

### 05_vectors/ - Dependent Types with Vectors
- **vector_operations.cure**: Length-indexed vectors
  - Compile-time length checking
  - Type-safe operations preserving length
  - Map, zip, fold on vectors
  - Conversion between Vector and List

### 06_result_option/ - Error Handling
- **error_handling.cure**: Monadic error handling
  - Option type for optional values
  - Result type for success/failure
  - Safe operations (safe_divide, safe_head)
  - Mapping and chaining (map, flatMap)
  - Validation pipelines

### 07_fsm/ - Finite State Machines
- **counter.cure**: Counter FSMs
  - Simple counter with increment/decrement
  - Bounded counter with limits
  - Up-down counter with direction
  - Timer FSM with timeouts
- **traffic_light.cure**: Traffic light FSMs
  - Simple traffic light
  - Timed traffic light with duration
  - Pedestrian crossing light
  - Smart traffic light with sensors

### 08_higher_order/ - Higher-Order Functions
- **lambdas.cure**: Functional programming patterns
  - Lambda expressions (anonymous functions)
  - Functions returning functions
  - Function composition
  - Currying and partial application
  - Classic higher-order functions: map, filter, fold
  - Function pipelines

### 09_records/ - Record Types
- **records.cure**: Record data structures
  - Simple and generic records
  - Field access with dot notation
  - Immutable updates
  - Pattern matching on records
  - Nested records

### 11_io/ - Input/Output
- **io_examples.cure**: Console I/O
  - Basic printing with print/println
  - Formatted output
  - Debug and error messages
  - Status reporting and progress indication

### 12_math/ - Mathematical Operations
- **math_operations.cure**: Using Std.Math
  - Constants: pi, e
  - Basic operations: abs, sign, negate
  - Arithmetic: add, subtract, multiply
  - Min/max and clamping
  - Power function
  - Practical examples: distance, average, factorial

## Standard Library Examples

Each example demonstrates functions from the Cure standard library (`lib/std/`):

- **Std.List**: List operations (map, filter, fold, zip_with, etc.)
- **Std.Vector**: Length-indexed vector operations
- **Std.Core**: Core functions (identity, compose, comparison)
- **Std.Result**: Result type operations
- **Std.Fsm**: FSM runtime operations
- **Std.Io**: I/O operations
- **Std.Math**: Mathematical functions

## Key Language Features Demonstrated

### Dependent Types
```cure
def make_vector3<T>(x: T, y: T, z: T): Vector(T, 3) do
  [x, y, z]
end
```

### Pattern Matching with Guards
```cure
def classify(n: Int): Atom do
  match n do
    x when x > 0 -> :positive
    x when x < 0 -> :negative
    0 -> :zero
  end
end
```

### Finite State Machines
```cure
fsm Counter do
  state idle do
    on start -> counting(0)
  end
  
  state counting(value: Int) do
    on increment -> counting(value + 1)
    on stop -> idle
  end
end
```

### Polymorphic Functions
```cure
def map<A, B>(list: List(A), f: A -> B): List(B) do
  match list do
    [] -> []
    [h | t] -> [f(h) | map(t, f)]
  end
end
```

### Records
```cure
record Person do
  name: String
  age: Int
  email: String
end

let person = Person{name: "Alice", age: 30, email: "alice@example.com"}
let updated = Person{person | age: 31}
```

### Higher-Order Functions
```cure
def compose<A, B, C>(f: B -> C, g: A -> B): A -> C do
  fn(x) -> f(g(x)) end
end
```

## Running Examples

To compile and run an example:

```bash
# Build the compiler
make all

# Compile an example
./cure compile examples/01_basics/literals.cure

# Run the compiled module
erl -pa _build/ebin -eval 'Literals:main(), init:stop().'
```

## Testing Examples

All examples are designed to:
- Compile without errors
- Demonstrate correct usage of language features
- Follow best practices for Cure programming
- Include comprehensive comments explaining each feature

## Learning Path

Recommended order for learning Cure:

1. **01_basics/** - Start here to understand fundamental syntax
2. **03_patterns/** - Learn pattern matching (essential for Cure)
3. **02_types/** - Understand the type system
4. **04_lists/** - Practice with standard library
5. **06_result_option/** - Learn error handling patterns
6. **08_higher_order/** - Master functional programming
7. **09_records/** - Work with structured data
8. **05_vectors/** - Explore dependent types
9. **07_fsm/** - Build state machines
10. **11_io/, 12_math/** - Use standard library modules

## Additional Resources

- See `WARP.md` in the project root for compiler architecture details
- Check `lib/std/` for standard library implementations
- Refer to `src/parser/cure_ast.hrl` for complete AST definitions
- Review test files in `test/` for more usage examples

## Contributing Examples

When adding new examples:
1. Create a new subdirectory or add to an existing category
2. Include comprehensive comments explaining each feature
3. Ensure examples compile and run successfully
4. Add a main/0 function for easy testing
5. Update this README with the new example

## License

These examples are part of the Cure programming language project.
