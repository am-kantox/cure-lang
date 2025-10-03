# Cure Type System

## Overview

Cure features a dependent type system that allows types to depend on values, enabling more precise specification of program behavior and catching more errors at compile time.

## Table of Contents

1. [Basic Types](#basic-types)
2. [Dependent Types](#dependent-types)
3. [Type Inference](#type-inference)
4. [Constraint Solving](#constraint-solving)
5. [Refinement Types](#refinement-types)
6. [Type Checking Algorithm](#type-checking-algorithm)
7. [Examples](#examples)
8. [Implementation](#implementation)

## Basic Types

### Primitive Types

```cure
Int      # 64-bit signed integers: ..., -1, 0, 1, ...
Float    # 64-bit IEEE floating point: 3.14, -2.5, 1.0e10
String   # UTF-8 strings: "hello", "world"
Bool     # Boolean values: true, false
Atom     # Symbolic constants: :ok, :error, :undefined
```

### Composite Types

```cure
List(T)           # Homogeneous lists: [1, 2, 3], ["a", "b"]
List(T, n)        # Length-indexed lists: List(Int, 3) = [1, 2, 3]
Tuple(T1, T2, ..) # Fixed-size tuples: (1, "hello", true)
```

### Function Types

```cure
(T1, T2, ...) -> R    # Function from T1, T2, ... to R
```

## Dependent Types

Dependent types allow type expressions to contain value expressions, enabling precise specification of program properties.

### Basic Dependent Types

```cure
# Arrays with statically known size
Array(T, n)   where n: Nat

# Lists with length constraints  
List(T, n)    where n: Nat

# Integers with range constraints
Int{min..max} where min <= max
```

### Predicate Types

Types can be refined with boolean predicates:

```cure
# Natural numbers (non-negative integers)
Nat = Int where x >= 0

# Positive integers  
Pos = Int where x > 0

# Even numbers
Even = Int where x % 2 == 0

# Non-empty lists
NonEmpty(T) = List(T, n) where n > 0
```

### Examples

```cure
# Safe array indexing
def get_element(arr: Array(T, n), i: Int) -> T when 0 <= i < n =
  unsafe_get(arr, i)

# Safe division
def safe_divide(x: Float, y: Float) -> Float when y != 0.0 =
  x / y

# List concatenation preserves length
def concat(xs: List(T, n), ys: List(T, m)) -> List(T, n+m) =
  append_lists(xs, ys)
```

## Type Inference

Cure uses a constraint-based type inference algorithm that can infer types even in the presence of dependent types.

### Algorithm Overview

1. **Constraint Generation**: Generate type constraints from the AST
2. **Constraint Solving**: Solve constraints using unification and SMT solving
3. **Type Reconstruction**: Build final types from constraint solutions

### Type Variables

```cure
# Before inference
def identity(x) = x

# After inference  
def identity(x: 'a) -> 'a = x
```

### Constraint Propagation

```cure
def safe_head(list) =
  match list do
    [x | _] -> x
  end

# Inferred type:
# safe_head : List(T, n) -> T when n > 0
```

## Constraint Solving

The type checker maintains a constraint store and solves constraints incrementally.

### Constraint Types

1. **Equality Constraints**: `T1 = T2`
2. **Subtyping Constraints**: `T1 <: T2`  
3. **Predicate Constraints**: `P(x1, x2, ...)`

### SMT Integration

Complex constraints are solved using an SMT solver:

```cure
def matrix_multiply(a: Matrix(m, k), b: Matrix(k, n)) -> Matrix(m, n) = ...
#                              ^              ^
#                              |              |
#                        These must be equal
```

### Constraint Examples

```cure
# Generates constraint: length(xs) > 0
def head(xs: List(T, n)) -> T when n > 0 = ...

# Generates constraint: i >= 0 ∧ i < length(arr)  
def get(arr: Array(T, n), i: Int) -> T when 0 <= i < n = ...
```

## Refinement Types

Refinement types extend base types with predicates that must hold for all values of that type.

### Syntax

```cure
{x: BaseType | Predicate(x)}
```

### Built-in Refinement Types

```cure
# Natural numbers
Nat = {x: Int | x >= 0}

# Positive integers
Pos = {x: Int | x > 0}

# Non-zero numbers
NonZero = {x: Float | x != 0.0}

# Bounded integers
Bounded(min, max) = {x: Int | min <= x <= max}

# Non-empty strings
NonEmptyString = {s: String | length(s) > 0}
```

### Custom Refinement Types

```cure
# Prime numbers
Prime = {x: Int | is_prime(x)}

# Sorted lists
Sorted(T) = {xs: List(T) | is_sorted(xs)}

# Balanced trees
Balanced(T) = {tree: Tree(T) | is_balanced(tree)}
```

## Type Checking Algorithm

### Overview

The type checker uses a bidirectional typing algorithm with constraint generation:

```
Γ ⊢ e ⇒ τ | C    # Expression e has type τ under context Γ with constraints C
Γ ⊢ e ⇐ τ | C    # Expression e checks against type τ under context Γ with constraints C
```

### Rules

#### Variables

```
x : τ ∈ Γ
─────────────
Γ ⊢ x ⇒ τ | ∅
```

#### Function Application

```
Γ ⊢ f ⇒ (τ1, ..., τn) -> τ | C1
Γ ⊢ e1 ⇐ τ1 | C2
...
Γ ⊢ en ⇐ τn | Cn
─────────────────────────────────
Γ ⊢ f(e1, ..., en) ⇒ τ | C1 ∪ ... ∪ Cn
```

#### Dependent Function Types

```
Γ, x1 : τ1, ..., xn : τn ⊢ body ⇐ τ | C1
Γ, x1 : τ1, ..., xn : τn ⊢ constraint | C2
─────────────────────────────────────────────────────────────
Γ ⊢ def f(x1: τ1, ..., xn: τn) -> τ when constraint = body ⇒ 
    (τ1, ..., τn) -> τ when constraint | C1 ∪ C2
```

## Examples

### Safe List Operations

```cure
# Safe head function
def head(xs: List(T, n)) -> T when n > 0 =
  match xs do [y | _] -> y end

# Safe tail function  
def tail(xs: List(T, n)) -> List(T, n-1) when n > 0 =
  match xs do [_ | ys] -> ys end

# List indexing
def get(xs: List(T, n), i: Int) -> T when 0 <= i < n =
  if i == 0 then head(xs)
  else get(tail(xs), i - 1)
  end
```

### Arithmetic Operations

```cure
# Safe division
def divide(x: Float, y: Float) -> Float when y != 0.0 =
  x / y

# Integer square root  
def isqrt(x: Int) -> Int when x >= 0 =
  floor(sqrt(float(x)))

# Factorial with precise type
def factorial(n: Nat) -> Pos when n > 0 =
  if n == 1 then 1
  else n * factorial(n - 1)
  end
```

### Matrix Operations

```cure
# Matrix addition requires same dimensions
def add_matrices(a: Matrix(m, n), b: Matrix(m, n)) -> Matrix(m, n) =
  element_wise_add(a, b)

# Matrix multiplication has dimension constraint
def multiply_matrices(a: Matrix(m, k), b: Matrix(k, n)) -> Matrix(m, n) =
  matrix_mult_impl(a, b)
```

### FSM Type Safety

```cure
fsm Counter do
  states: [Zero, Pos(n) where n > 0]
  initial: Zero
  
  state Zero do
    event(:inc) -> Pos(1)
  end
  
  state Pos(n) do
    event(:inc) -> Pos(n + 1)
    event(:dec) -> if n == 1 then Zero else Pos(n - 1) end
  end
end

# Type-safe FSM usage
def increment_counter(fsm: CounterFSM) -> Unit =
  fsm_send(fsm, :inc)
```

## Implementation

### Core Components

1. **cure_types.erl**: Core type system implementation
2. **cure_typechecker.erl**: High-level type checking interface
3. **cure_constraints.erl**: Constraint generation and solving
4. **cure_unify.erl**: Type unification algorithm

### Type Representation

Types are represented as Erlang terms:

```erlang
% Basic types
{basic_type, int}
{basic_type, float}
{basic_type, string}
{basic_type, bool}
{basic_type, atom}

% Function types
{function_type, [Param1, Param2, ...], ReturnType}

% Dependent types
{dependent_type, BaseType, Constraints}

% List types with length
{list_type, ElementType, LengthExpr}

% Refinement types
{refinement_type, BaseType, Predicate}
```

### Constraint Representation

```erlang
% Equality constraint
{eq_constraint, Type1, Type2}

% Subtyping constraint  
{subtype_constraint, Type1, Type2}

% Predicate constraint
{predicate_constraint, Predicate, Args}
```

### Algorithm Complexity

- **Type inference**: O(n³) where n is program size
- **Constraint solving**: Depends on SMT solver (typically exponential worst-case)
- **Unification**: O(n log n) for most cases
- **Space**: O(n²) for constraint storage

### Performance Optimizations

1. **Constraint simplification**: Eliminate redundant constraints
2. **Early constraint checking**: Fail fast on unsolvable constraints
3. **Incremental solving**: Solve constraints as they're generated
4. **Caching**: Cache solved constraint sets

## Error Messages

The type checker provides detailed error messages:

```cure
# Example error
def bad_divide(x: Int, y: Int) -> Int =
  x / y  # Error: Division requires non-zero divisor

# Error message:
Type error in function bad_divide at line 2:
  Expression: x / y
  Problem: Cannot prove constraint 'y != 0'
  
  The function divide requires its second argument to be non-zero,
  but no such constraint exists on parameter 'y'.
  
  Suggestion: Add constraint 'when y != 0' to function signature
```

## Future Extensions

### Planned Features

1. **Liquid types**: More sophisticated refinement types
2. **Linear types**: Resource usage tracking
3. **Effect types**: Side effect specification
4. **Gradual typing**: Mixed static/dynamic typing
5. **Type-level computation**: More expressive dependent types

### Research Directions

1. **Inference improvements**: Better constraint solving
2. **Performance**: Faster type checking algorithms  
3. **Expressiveness**: More powerful type system features
4. **Usability**: Better error messages and tooling