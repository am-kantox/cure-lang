# Cure Language Examples

This directory contains comprehensive examples demonstrating the core features of the Cure programming language. Each example file focuses on a specific aspect of the language and provides practical demonstrations.

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

### 3. Dependent Types (`dependent_types.cure`)

Demonstrates compile-time guarantees and type safety through dependent types:

- **Length-Indexed Vectors**: Vectors with compile-time known lengths
- **Matrix Operations**: Dimension checking at compile time
- **Refinement Types**: Types with predicates (`{x: Int | x > 0}`)
- **Indexed Data Structures**: Binary trees with depth tracking
- **Phantom Types**: Unit safety (meters vs feet)
- **GADTs**: Type-safe expression evaluation
- **Proof Carrying Code**: Types that maintain invariants

**Key Features Shown:**
```cure
# Length-safe vector operations
def dot_product(v1: Vector(Float, n), v2: Vector(Float, n)): Float =
  # Type system guarantees same length

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