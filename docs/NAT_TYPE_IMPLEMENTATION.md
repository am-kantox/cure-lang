# Nat Type Implementation - Idris-Style Peano Encoding

## Overview

The `Nat` type has been successfully introduced to Cure using Peano encoding, similar to Idris's natural number representation. This provides a foundation for dependent type programming with compile-time arithmetic verification.

## Implementation Details

### 1. Type Definition (`src/types/cure_types.erl`)

```erlang
%% Nat type as algebraic data type (Peano encoding, like Idris)
%% data Nat = Zero | Succ Nat
-define(TYPE_NAT, {union_type, 'Nat', 
    [{'Zero', {primitive_type, 'Nat'}},
     {'Succ', {function_type, [{primitive_type, 'Nat'}], {primitive_type, 'Nat'}}}],
    undefined}).
```

**Comparison with Idris:**
- Idris: `data Nat = Z | S Nat`
- Cure: `data Nat = Zero | Succ Nat`

### 2. Helper Functions

Five new exported functions in `cure_types.erl`:

- **`nat_zero/0`**: Creates the Zero constructor
- **`nat_succ/1`**: Creates a successor (Succ) constructor
- **`nat_from_int/1`**: Converts Erlang integer → Peano Nat
- **`nat_to_int/1`**: Converts Peano Nat → Erlang integer
- **`is_nat_type/1`**: Type predicate for Nat checking

### 3. Lexer Support (`src/lexer/cure_lexer.erl`)

Added three new keywords:
- `Nat` - The type itself
- `Zero` - Nullary constructor (represents 0)
- `Succ` - Unary constructor (represents n+1)

### 4. Parser Support (`src/parser/cure_parser.erl`)

Enhanced `parse_primary_type/1` to recognize:
- `Nat` as a primitive type
- `Zero` as a nullary constructor
- `Succ` as a type constructor accepting one Nat argument

### 5. Example Code (`examples/nat_type_demo.cure`)

Demonstrates:
- **Addition**: Recursive Peano addition
- **Multiplication**: Defined via repeated addition
- **Conversion**: Bidirectional Int ↔ Nat conversion

```cure
def plus(x: Nat, y: Nat): Nat =
  match x do
    Zero -> y
    Succ(pred) -> Succ(plus(pred, y))
  end
```

### 6. Test Suite (`test/nat_type_test.erl`)

Comprehensive EUnit tests covering:
- Constructor creation
- Type checking and unification
- Conversion functions
- Round-trip Int ↔ Nat conversion
- Pattern matching

### 7. Documentation (`docs/TYPE_SYSTEM.md`)

Added comprehensive documentation including:
- Nat type definition and syntax
- Peano encoding examples
- Recursive function patterns
- Benefits for dependent type programming

## Usage Examples

### Basic Construction

```cure
let zero = Zero
let one = Succ(Zero)
let two = Succ(Succ(Zero))
let three = Succ(Succ(Succ(Zero)))
```

### Recursive Functions

```cure
def plus(x: Nat, y: Nat): Nat =
  match x do
    Zero -> y
    Succ(pred) -> Succ(plus(pred, y))
  end

def times(x: Nat, y: Nat): Nat =
  match x do
    Zero -> Zero
    Succ(pred) -> plus(y, times(pred, y))
  end
```

### Conversion

```cure
## Erlang side
{ok, Five} = cure_types:nat_from_int(5),
%% Results in: Succ(Succ(Succ(Succ(Succ(Zero)))))

{ok, 5} = cure_types:nat_to_int(Five).
```

## Benefits

### 1. Type-Level Computation
```cure
Vector(T, n: Nat)  # Length-indexed vectors
Array(T, n: Nat)   # Sized arrays with compile-time bounds
```

### 2. Totality Checking
Pattern matches on Nat are exhaustive:
```cure
match n do
  Zero -> ...       # Handles 0
  Succ(m) -> ...    # Handles n > 0
end
```

### 3. Dependent Types
```cure
def replicate(n: Nat, x: T): Vector(T, n) =
  match n do
    Zero -> []
    Succ(m) -> x :: replicate(m, x)
  end
```

### 4. Compile-Time Verification
```cure
def get_at(vec: Vector(T, n), i: Nat): T when i < n =
  # Type system verifies i is within bounds
  unsafe_get(vec, i)
```

## Comparison with Refinement Types

Cure supports **two** representations of natural numbers:

### 1. Algebraic Nat (Peano)
```cure
data Nat = Zero | Succ Nat

let three = Succ(Succ(Succ(Zero)))
```

**Benefits:**
- Structural induction
- Type-level computation
- Pattern matching
- Idris-style dependent programming

### 2. Refined Int
```cure
type NatRefined = Int where x >= 0

let three: NatRefined = 3
```

**Benefits:**
- Efficient runtime representation
- SMT-based constraint solving
- Direct arithmetic operations

## Future Enhancements

1. **Standard Library Functions**
   - `minus`, `div`, `mod` for Nat
   - Comparison operators
   - Conversion utilities

2. **Type-Level Arithmetic**
   - Enable Nat expressions in types: `Vector(T, n+m)`
   - Compile-time evaluation of Nat operations

3. **Proofs and Verification**
   - Totality checker for recursive functions
   - Termination proofs using Nat induction

4. **Optimizations**
   - Convert Peano Nat to Int at runtime when safe
   - Fusion of Nat operations

## Files Modified

- ✅ `src/types/cure_types.erl` - Type definition and helpers
- ✅ `src/lexer/cure_lexer.erl` - Keyword recognition
- ✅ `src/parser/cure_parser.erl` - Parser support
- ✅ `examples/nat_type_demo.cure` - Usage examples
- ✅ `test/nat_type_test.erl` - Test suite
- ✅ `docs/TYPE_SYSTEM.md` - Documentation

## References

- **Idris Documentation**: [Nat type in Idris](https://docs.idris-lang.org/en/latest/tutorial/theorems.html)
- **Dependent Types**: Pierce, B. C. (2002). Types and Programming Languages
- **Peano Arithmetic**: Peano, G. (1889). Arithmetices principia, nova methodo exposita
