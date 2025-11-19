# Cure Dependent Types - User Guide

## Table of Contents
1. [Introduction](#introduction)
2. [Basic Syntax](#basic-syntax)
3. [Common Patterns](#common-patterns)
4. [SMT-Based Verification](#smt-based-verification)
5. [Standard Library Integration](#standard-library-integration)
6. [Advanced Examples](#advanced-examples)
7. [Best Practices](#best-practices)
8. [Troubleshooting](#troubleshooting)

---

## Introduction

Cure's dependent types allow types to depend on **values**, enabling compile-time verification of invariants that traditionally require runtime checks. This leads to:

- **Zero-cost safety**: No runtime bounds checks needed
- **Compile-time guarantees**: Catch errors before code runs
- **Better documentation**: Types express precise contracts
- **Verified correctness**: SMT solver proves properties automatically

### Example: Traditional vs Dependent Types

```cure
%% Traditional approach: Runtime error possible
def head(xs: List(Int)): Int =
    match xs with
    | [x | _] -> x
    | [] -> error("empty list!")  % ⚠️ Runtime error!
    end

%% Dependent types: Compile-time safety
def safe_head<T, n: Nat>(xs: Vector(T, n + 1)): T =
    match xs with
    | [x | _] -> x
    % ✓ No error case needed! Compiler proves xs is non-empty
    end
```

---

## Basic Syntax

### Dependent Type Definitions

```cure
%% Syntax: type Name(value_params...) = BaseType where constraints
type Vector(T, n: Nat) = List(T) where length(this) == n

%% Refined types with constraints
type NonEmpty(T) = List(T) where length(this) > 0
type Index(n: Nat) = Int where 0 <= this < n
type Percentage = Int where 0 <= this <= 100
```

### Type Parameters

Cure distinguishes between **type parameters** (types) and **value parameters** (runtime values):

```cure
def example<T, n: Nat>(v: Vector(T, n)) =
    %     ^  ^^^^^
    %     |    |
    %  Type  Value parameter (Nat)
    % parameter
```

### Where Clauses

Constraints use `where` clauses with predicates:

```cure
type BoundedInt(min: Int, max: Int) = Int 
    where min <= this <= max

type SortedList(T) = List(T) 
    where forall i, j. (i < j) => (nth(this, i) <= nth(this, j))
```

---

## Common Patterns

### 1. Safe Head/Tail Operations

```cure
def head<T, n: Nat>(v: Vector(T, n + 1)): T =
    match v with
    | [x | _] -> x
    end

def tail<T, n: Nat>(v: Vector(T, n + 1)): Vector(T, n) =
    match v with
    | [_ | xs] -> xs
    end

%% Usage
let v = [1, 2, 3] in  % Type: Vector(Int, 3)
let x = head(v)       % Safe! 3 = n + 1, so n = 2
let rest = tail(v)    % Type: Vector(Int, 2)
```

**Why it works**: The type `Vector(T, n + 1)` requires `n + 1 >= 1`, so the vector is provably non-empty.

### 2. Safe Indexing

```cure
type Index(n: Nat) = Int where 0 <= this < n

def nth<T, n: Nat>(v: Vector(T, n), i: Index(n)): T =
    nth_impl(v, i)

%% Usage
let v = [10, 20, 30] in  % Type: Vector(Int, 3)
let i: Index(3) = 1 in   % Compiler verifies 0 <= 1 < 3
nth(v, i)  % Returns 20, no bounds check!
```

**Why it works**: `Index(n)` can only hold values in `[0, n)`, so indexing is always safe.

### 3. Length Arithmetic

```cure
def concat<T, m: Nat, n: Nat>(
    v1: Vector(T, m),
    v2: Vector(T, n)
): Vector(T, m + n) =
    v1 ++ v2

def split<T, n: Nat, k: Nat where k <= n>(
    v: Vector(T, n),
    at: k
): {Vector(T, k), Vector(T, n - k)} =
    {take(v, k), drop(v, k)}
```

**Why it works**: The type system tracks lengths through arithmetic operations (`m + n`, `n - k`).

### 4. Matrix Dimensions

```cure
type Matrix(T, rows: Nat, cols: Nat) = 
    Vector(Vector(T, cols), rows)

def transpose<T, m: Nat, n: Nat>(
    matrix: Matrix(T, m, n)
): Matrix(T, n, m) =
    %% Implementation

def multiply<T, m: Nat, n: Nat, p: Nat>(
    a: Matrix(T, m, n),
    b: Matrix(T, n, p)
): Matrix(T, m, p) =
    %% Compiler ensures a.cols == b.rows (both are n)
```

**Why it works**: Matrix dimensions are tracked in types. Incompatible operations (e.g., multiplying 3×2 by 5×4) are rejected at compile time.

---

## SMT-Based Verification

Cure uses Z3 (an SMT solver) to prove type constraints automatically.

### How It Works

1. **Constraint Generation**: The type checker generates logical formulas (verification conditions)
2. **SMT Translation**: Formulas are translated to SMT-LIB2 format
3. **Z3 Verification**: Z3 proves the formula is satisfiable
4. **Result**: If proven, code compiles; otherwise, type error

### Example: Proving Non-Negativity

```cure
type Balance = Int where this >= 0

def deposit(balance: Balance, amount: Int where amount > 0): Balance =
    balance + amount
    %% Compiler generates VC: (balance >= 0 ∧ amount > 0) ⇒ (balance + amount >= 0)
    %% Z3 proves: ✓ sat
```

### SMT Logics Used

- **QF_LIA**: Quantifier-free linear integer arithmetic (default)
- **QF_LIRA**: Linear integer/real arithmetic (for mixed types)
- **AUFLIA**: Arrays with uninterpreted functions (for array theory)
- **QF_NIA**: Non-linear integer arithmetic (for multiplication/division)

### Controlling Verification

```cure
%% Provide hints to the SMT solver
def complex_function(x: Int, y: Int): Int 
    where x > 0, y > 0, x + y < 100  % Multiple constraints
=
    %% SMT solver receives all constraints as assumptions
    x * y

%% Explicit assertions (checked at compile time)
def verified_property(n: Nat): Nat 
    where n > 0
=
    let result = n * 2 in
    assert result > n  % Proven by SMT
    result
```

---

## Standard Library Integration

### Vector Module

The standard library (`lib/std/vector.cure`) provides common operations:

```cure
module Vector do
    def length<T>(v: List(T)): Nat
    def is_empty<T>(v: List(T)): Bool
    def reverse<T, n: Nat>(v: Vector(T, n)): Vector(T, n)
    def map<T, U, n: Nat>(f: T -> U, v: Vector(T, n)): Vector(U, n)
    def filter<T, n: Nat>(pred: T -> Bool, v: Vector(T, n)): Vector(T, m) where m <= n
    def fold<T, U, n: Nat>(f: (U, T) -> U, init: U, v: Vector(T, n)): U
    def zip_with<T, U, V, n: Nat>(f: (T, U) -> V, v1: Vector(T, n), v2: Vector(U, n)): Vector(V, n)
    def contains<T, n: Nat>(v: Vector(T, n), elem: T): Bool
end
```

### Using Dependent Types with Vector

```cure
import Vector

%% Safe operations with compile-time guarantees
def process_data(): Vector(Int, 5) =
    let data = [1, 2, 3, 4, 5] in  % Type: Vector(Int, 5)
    let doubled = Vector.map(fn x -> x * 2, data) in  % Type: Vector(Int, 5)
    let reversed = Vector.reverse(doubled) in  % Type: Vector(Int, 5)
    reversed

%% No runtime length checks needed!
def get_first_three<T, n: Nat where n >= 3>(v: Vector(T, n)): Vector(T, 3) =
    Vector.take(v, 3)  % Compiler verifies n >= 3
```

---

## Advanced Examples

### Example 1: State Machines with Invariants

```cure
fsm Counter do
    type Count = Int where 0 <= this <= 100
    
    payload: {count: Count}
    
    state Counting(count: Count) do
        on increment() when count < 100 ->
            Counting { count = count + 1 }
            %% Compiler proves: count < 100 ⇒ count + 1 <= 100
        
        on decrement() when count > 0 ->
            Counting { count = count - 1 }
            %% Compiler proves: count > 0 ⇒ count - 1 >= 0
        
        on reset() -> Counting { count = 0 }
    end
    
    invariant: 0 <= count <= 100  % Verified automatically!
end
```

### Example 2: Sorted Lists

```cure
type Sorted(T) = List(T) where is_sorted(this)

def merge<T, m: Nat, n: Nat>(
    xs: Sorted(Vector(T, m)),
    ys: Sorted(Vector(T, n))
): Sorted(Vector(T, m + n)) =
    merge_impl(xs, ys)
    %% Compiler verifies: sorted(xs) ∧ sorted(ys) ⇒ sorted(merge(xs, ys))

def insert<T, n: Nat>(
    x: T,
    xs: Sorted(Vector(T, n))
): Sorted(Vector(T, n + 1)) =
    insert_impl(x, xs)
    %% Compiler verifies: sorted(xs) ⇒ sorted(insert(x, xs))
```

### Example 3: Dependent Records

```cure
type Person = {
    name: String where length(name) > 0,
    age: Int where 0 <= age <= 150,
    email: String where is_valid_email(email)
}

def create_person(name: String, age: Int, email: String): Option(Person) =
    %% Compiler verifies all constraints before constructing
    if length(name) > 0 && 0 <= age <= 150 && is_valid_email(email) then
        Some({name, age, email})
    else
        None
```

---

## Best Practices

### 1. Start Simple

Begin with basic refinement types, then add dependent types:

```cure
%% Step 1: Basic type
def process(xs: List(Int)): Int

%% Step 2: Add refinement
def process(xs: NonEmpty(Int)): Int

%% Step 3: Add dependent type
def process<n: Nat>(xs: Vector(Int, n + 1)): Int
```

### 2. Use Meaningful Names

```cure
%% ❌ Bad: Unclear what 'n' represents
def foo<T, n: Nat>(v: Vector(T, n)) = ...

%% ✓ Good: Clear parameter names
def resize<T, old_size: Nat, new_size: Nat>(
    v: Vector(T, old_size),
    target_size: new_size
): Vector(T, new_size) = ...
```

### 3. Document Assumptions

```cure
%% Document why constraints are needed
def binary_search<T, n: Nat>(
    v: Sorted(Vector(T, n)),  % Must be sorted for binary search
    target: T
): Option(Index(n)) =
    %% Implementation assumes v is sorted
```

### 4. Leverage Inference

Let the compiler infer types when possible:

```cure
%% Explicit (verbose)
def demo(): Vector(Int, 3) =
    let v: Vector(Int, 5) = [1, 2, 3, 4, 5] in
    let result: Vector(Int, 3) = take(v, 3) in
    result

%% Inferred (concise)
def demo(): Vector(Int, 3) =
    take([1, 2, 3, 4, 5], 3)  % Compiler infers all types
```

### 5. Balance Precision and Complexity

Not every function needs dependent types:

```cure
%% ✓ Good: Dependent types add value
def head<T, n: Nat>(v: Vector(T, n + 1)): T

%% ❌ Overkill: Complexity doesn't justify benefit
def add(x: Int where x > 0, y: Int where y > 0): Int where this == x + y
```

---

## Troubleshooting

### Error: "Cannot prove constraint"

**Problem**: SMT solver cannot verify a constraint.

```cure
def example(n: Nat): Nat =
    n - 1  % ERROR: Cannot prove (n - 1) >= 0
```

**Solution**: Add explicit bounds:

```cure
def example(n: Nat where n > 0): Nat =
    n - 1  % ✓ OK: SMT proves (n > 0) ⇒ (n - 1 >= 0)
```

### Error: "Type mismatch in dependent types"

**Problem**: Length/dimension mismatch.

```cure
def bad_concat(): Vector(Int, 5) =
    concat([1, 2], [3, 4])  % ERROR: 2 + 2 ≠ 5
```

**Solution**: Fix the expected type:

```cure
def good_concat(): Vector(Int, 4) =
    concat([1, 2], [3, 4])  % ✓ OK: 2 + 2 = 4
```

### Error: "SMT solver timeout"

**Problem**: Constraint too complex for Z3.

```cure
def complex(n: Nat): Nat where some_very_complex_property(n) =
    %% Z3 times out
```

**Solutions**:
1. **Simplify constraints**: Break into smaller pieces
2. **Add intermediate assertions**: Guide the solver
3. **Increase timeout**: Configure solver timeout (default: 5s)
4. **Use runtime checks**: Fall back to assertions for very complex properties

### Debugging Tips

1. **Check SMT output**: Use `--dump-smt` flag to see generated SMT-LIB2
   ```bash
   curc --dump-smt example.cure
   ```

2. **Simplify constraints**: Comment out constraints one by one to isolate the issue

3. **Add explicit types**: Help the type checker by annotating intermediate values

4. **Use `assert`**: Runtime assertions can complement compile-time checks

---

## Performance Considerations

### Benefits
- **No runtime checks**: Bounds/null checks eliminated by compiler
- **Better optimizations**: Static lengths enable SIMD, unrolling
- **Smaller binaries**: No error-handling code for proven-safe operations

### Costs
- **Compile time**: SMT verification adds overhead (typically <100ms per function)
- **Code size**: Monomorphization may duplicate code for different lengths

### Tuning

```cure
%% Control optimization vs. compile time
@optimization_level(3)  % More aggressive optimization
def hot_path<T, n: Nat>(v: Vector(T, n)): T =
    %% Compiler may specialize for common n values (e.g., n=1,2,3,4,8,16)

@no_smt_verify  % Skip SMT verification (use with caution!)
def trusted_function(x: Int): Int =
    %% Manual verification performed, skip SMT
```

---

## Further Reading

- **Design Document**: `docs/DEPENDENT_TYPES_DESIGN.md` - Detailed design rationale
- **Examples**: `examples/dependent_types_demo.cure` - Comprehensive examples
- **Implementation**: `src/types/cure_dependent_types.erl` - Type checker source
- **SMT Integration**: `docs/SMT_INTEGRATION.md` - SMT solver details

---

## Summary

Cure's dependent types bring the power of formal verification to everyday programming:

✅ **Safe**: No runtime bounds errors  
✅ **Fast**: Zero-cost abstractions  
✅ **Expressive**: Types document invariants  
✅ **Verified**: SMT proves correctness  
✅ **Practical**: Works with existing BEAM code

Start using dependent types today to write safer, faster Cure programs!
