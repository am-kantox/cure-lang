# Cure Language Examples

🚀 **NEW: Complete Import System & Runtime Success!** (October 2025)

This directory contains comprehensive examples demonstrating the core features of the Cure programming language, including **working examples with full import system integration**. Each example file focuses on a specific aspect of the language and provides practical demonstrations.

## 🎆 Featured Working Example: `dependent_types_simple.cure`

**BREAKTHROUGH**: This example successfully compiles and runs with the complete import system!

```bash
# Compile and run
./cure examples/dependent_types_simple.cure
erl -pa _build/ebin -noshell -eval "'DependentTypes':demo_all(), init:stop()."

# Output:
=== Dependent Types Demonstration ===
All operations below are compile-time verified for safety!
=== Vector Operations ===
Dot product: 32.0
Vector sum: [5.0, 7.0, 9.0] 
Scaled vector: [2.0, 4.0, 6.0]
```

**Features Demonstrated**:
- ✅ **Working import system**: `import Std [List, Result]`
- ✅ **Standard library functions**: `print/1`, `show/1`, `map/2`, `fold/3`, `zip_with/3`
- ✅ **Dependent types**: Length-indexed vectors with compile-time safety
- ✅ **Runtime execution**: Full end-to-end compilation and execution
- ✅ **Type safety**: Vector operations validated at compile time

## Example Files

### 1. Pattern Matching (`pattern_matching.cure`)

Demonstrates comprehensive pattern matching capabilities including:

- **Basic Pattern Matching**: Simple value matching with wildcards
- **List Pattern Matching**: Head/tail destructuring (`[head | tail]`)  
- **Guard Clauses**: Pattern matching with `when` conditions
- **Record Pattern Matching**: Destructuring records with field extraction
- **Union Type Matching**: Pattern matching on algebraic data types
- **Nested Patterns**: Complex nested pattern matching scenarios
- **Case Expressions**: Alternative syntax to `match` expressions
- **Tuple Patterns**: Destructuring tuples and coordinate processing

**Key Features Shown:**
```cure
# Guards with patterns
match n do
  x when x < 0 -> "negative"
  x when x > 100 -> "large positive"
  x -> "other: " ++ show(x)
end

# Record pattern matching
match Person{name: name, age: age} when age >= 18 ->
  "Adult: " ++ name
```

### 2. Monadic Pipes (`monadic_pipes.cure`)

Shows function composition and error handling using pipe operators:

- **Basic Pipe Operations**: Simple function composition with `|>`
- **Result Monadic Pipes**: Error-handling pipelines that short-circuit on failure
- **Option Monadic Pipes**: Safe operations with `Some`/`None` handling
- **List Processing Pipes**: Functional programming with lists
- **Complex Data Pipelines**: Multi-stage data processing with validation
- **Async Pipeline Simulation**: Composing asynchronous operations

**Key Features Shown:**
```cure
# Monadic pipeline with error handling
def process_user(raw_user): Result(ProcessedUser, ValidationError) =
  raw_user
  |> parse_user()
  |> bind(validate_user)
  |> bind(enrich_user)
  |> map(normalize_user)

# List processing pipeline
numbers
|> filter(fn(x) -> x > 0 end)
|> map(fn(x) -> x * 2 end)
|> sort()
```

### 3. Dependent Types 🚀 **WORKING WITH IMPORT SYSTEM!**

**🎆 `dependent_types_simple.cure`** - **BREAKTHROUGH**: Full compilation and runtime success!
**🎆 `dependent_types.cure`** - Advanced dependent types demonstrations

Demonstrates compile-time guarantees and type safety through dependent types:

- **✅ Length-Indexed Vectors**: Vectors with compile-time known lengths (**WORKING!**)
- **✅ Import System Integration**: Uses `import Std [List, Result]` (**WORKING!**)
- **✅ Standard Library Functions**: `zip_with/3`, `fold/3`, `map/2`, `show/1`, `print/1` (**WORKING!**)
- **Matrix Operations**: Dimension checking at compile time
- **Refinement Types**: Types with predicates (`{x: Int | x > 0}`)
- **Indexed Data Structures**: Binary trees with depth tracking
- **Phantom Types**: Unit safety (meters vs feet)
- **GADTs**: Type-safe expression evaluation
- **Proof Carrying Code**: Types that maintain invariants

**Key Features Shown:**
```cure
# 🚀 WORKING: Length-safe vector operations with imports
module DependentTypes do
  import Std [List, Result]  # Working import system!
  
  def dot_product(v1: Vector(Float, n), v2: Vector(Float, n)): Float =
    # Type system guarantees same length
    zip_with(v1, v2, fn(x, y) -> x * y end)
    |> fold(0.0, fn(x, acc) -> acc + x end)
  
  def demo_all(): Unit =
    let v1 = make_vec3(1.0, 2.0, 3.0)
    let v2 = make_vec3(4.0, 5.0, 6.0)
    let result = dot_product(v1, v2)
    print("Dot product: " ++ show(result))  # Output: 32.0
end

# Matrix multiplication with dimension checking  
def matrix_multiply(a: Matrix(m, n, T), b: Matrix(n, p, T)): Matrix(m, p, T) =
  # Dimensions must be compatible

# Safe division with non-zero guarantee
def safe_divide(x: Float, y: NonZeroFloat): Float = x / y
```

### 4. Finite State Machines (`finite_state_machines.cure`)

Comprehensive FSM examples with process integration:

- **TCP Connection FSM**: Network protocol state management
- **Vending Machine FSM**: Business logic state machines
- **Game State FSM**: Application state management  
- **Workflow FSM**: Document approval workflows
- **FSM-Process Integration**: Combining FSMs with the actor model
- **Composable State Machines**: Higher-level FSM coordination

**Key Features Shown:**
```cure
fsm TcpConnection do
  states: [Closed, Listen, Established, FinWait1]
  initial: Closed
  
  state Closed do
    event(:listen) -> Listen
    event(:connect) -> SynSent
  end
  
  state Established do
    event(:close) -> FinWait1
    event({:data, payload: Binary}) -> Established
  end
end
```

## Running the Examples

Each example file contains a `demo_all/0` function that demonstrates all features:

```cure
# To run pattern matching examples
PatternMatching.demo_all()

# To run monadic pipes examples  
MonadicPipes.demo_all()

# To run dependent types examples
DependentTypes.demo_all()

# To run FSM examples
FiniteStateMachines.demo_all()
```

## Language Features Highlighted

### Type Safety
- Compile-time guarantees prevent runtime errors
- Dependent types ensure correctness by construction
- Pattern matching exhaustiveness checking

### Functional Programming
- Immutable data structures
- Higher-order functions and lambdas
- Monadic composition with `|>` operators

### Concurrent Programming  
- Actor model with lightweight processes
- Message passing with `send`/`receive`
- FSM integration with process supervision

### Advanced Type System
- Dependent types with value-level parameters
- Refinement types with logical constraints
- GADTs for type-safe interpreters
- Phantom types for domain modeling

## Code Organization

Each example demonstrates:
1. **Type Definitions**: Custom types and records
2. **Core Functions**: Primary functionality demonstrations  
3. **Helper Functions**: Supporting utilities
4. **Demo Functions**: Complete working examples
5. **Integration Examples**: How features work together

## Educational Value

These examples are designed to:
- Show practical applications of advanced type systems
- Demonstrate real-world patterns and idioms
- Illustrate the safety guarantees provided by the type system
- Show how different language features complement each other

The examples progress from basic concepts to advanced applications, making them suitable for learning the language incrementally while showing the power of dependent types and formal methods applied to practical programming problems.