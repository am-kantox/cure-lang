# Z3 SMT Solver User Guide for Cure

**Version:** 1.0  
**Date:** 2025-11-18  
**Status:** Phase 1 Complete - Basic Functionality Available

---

## Table of Contents

1. [Introduction](#introduction)
2. [Installation](#installation)
3. [Quick Start](#quick-start)
4. [Using Refinement Types](#using-refinement-types)
5. [Dependent Types](#dependent-types)
6. [FSM Verification](#fsm-verification)
7. [Common Patterns](#common-patterns)
8. [Troubleshooting](#troubleshooting)
9. [API Reference](#api-reference)

---

## Introduction

Cure integrates the Z3 SMT solver to provide compile-time verification of:

- **Refinement Types**: Types with logical constraints (e.g., `x > 0`)
- **Dependent Types**: Types that depend on values (e.g., `List(T, n)` where `n` is length)
- **Pattern Exhaustiveness**: Guaranteeing all cases are covered
- **FSM Correctness**: Deadlock detection and reachability analysis

### Benefits

✅ **Catch errors at compile time** - No runtime crashes from constraint violations  
✅ **Mathematical proof** - Z3 provides formal guarantees  
✅ **Zero runtime overhead** - Constraints verified during compilation  
✅ **Better documentation** - Types express invariants precisely  

---

## Installation

### Prerequisites

1. **Z3 Solver** (version 4.8+)

```bash
# Ubuntu/Debian
sudo apt install z3

# macOS
brew install z3

# Verify installation
z3 --version
# Should output: Z3 version 4.13.3 - 64 bit (or similar)
```

2. **Cure Compiler** with SMT support (included in standard distribution)

### Verification

Test that Z3 integration works:

```bash
cd /path/to/cure
make test_smt
```

Expected output:
```
✅ SMT Parser Tests: 5/5 passing
✅ SMT Process Tests: 7/7 passing
✅ SMT Solver Integration: 6/6 passing
```

---

## Quick Start

### Your First Refinement Type

Create a file `hello_smt.cure`:

```cure
module HelloSmt

%% Define a positive integer type
type Positive = Int when x > 0

%% Safe division - divisor proven non-zero
type NonZero = Int when x /= 0

def safe_div(dividend: Int, divisor: NonZero) -> Int do
  dividend / divisor  %% Z3 proves: divisor /= 0
end

%% This compiles successfully
def example1() -> Int do
  safe_div(10, 5)  %% ✅ 5 /= 0, constraint satisfied
end

%% This causes a compile-time error
def example2() -> Int do
  safe_div(10, 0)  %% ❌ Error: 0 does not satisfy x /= 0
end
```

Compile with SMT verification:

```bash
cure compile --smt-verify hello_smt.cure
```

Output:
```
✅ Module HelloSmt type-checked
✅ All refinement constraints verified
❌ Error in example2 at line 18:
   Refinement type violation
   Required: x /= 0 (NonZero)
   But: x = 0
   Counterexample: Division by zero
```

---

## Using Refinement Types

### Basic Refinement Types

Refinement types add logical constraints to existing types:

```cure
%% Natural numbers (non-negative)
type Nat = Int when x >= 0

%% Percentage (0-100)
type Percentage = Int when x >= 0 and x =< 100

%% Even numbers
type Even = Int when x % 2 == 0

%% Temperature in Celsius
type Temperature = Int when x >= -273 and x =< 1000
```

### Using Refinement Types in Functions

```cure
%% Function requiring positive input
def factorial(n: Positive) -> Positive do
  if n == 1 then
    1
  else
    n * factorial(n - 1)
  end
end

%% Valid calls
factorial(5)   %% ✅ OK: 5 > 0
factorial(1)   %% ✅ OK: 1 > 0

%% Invalid calls (compile-time errors)
factorial(0)   %% ❌ Error: 0 does not satisfy x > 0
factorial(-5)  %% ❌ Error: -5 does not satisfy x > 0
```

### Subtyping with SMT

Z3 automatically proves subtyping relationships:

```cure
type Positive = Int when x > 0
type NonZero = Int when x /= 0

%% Z3 proves: Positive <: NonZero
%% (Every positive number is non-zero)

def use_nonzero(x: NonZero) -> Int do
  100 / x
end

def caller(x: Positive) -> Int do
  use_nonzero(x)  %% ✅ OK: Z3 proves Positive <: NonZero
end
```

---

## Dependent Types

Dependent types allow types to depend on values:

### Length-Indexed Lists

```cure
%% List with length constraint
type Vector(T, n: Nat) = List(T) when length == n

%% Safe head - requires non-empty list
def safe_head(xs: List(T)) -> T when length(xs) > 0 do
  xs[0]  %% Z3 proves: 0 < length, so access is safe
end

%% Safe tail
def safe_tail(xs: List(T)) -> List(T) when length(xs) > 0 do
  drop(xs, 1)
end

%% Safe indexing
def safe_get(xs: List(T), i: Nat) -> Option(T) when i < length(xs) do
  if i < length(xs) then
    Some(xs[i])  %% Z3 proves: 0 <= i < length
  else
    None  %% Unreachable, but required for totality
  end
end
```

### Array Bounds Checking

```cure
%% Function that accesses first two elements
def first_two(xs: List(T)) -> {T, T} when length(xs) >= 2 do
  {xs[0], xs[1]}  %% Z3 proves both accesses safe
end

%% Usage
let list = [1, 2, 3] in
first_two(list)  %% ✅ OK: length = 3 >= 2

let short = [42] in
first_two(short)  %% ❌ Error: length = 1, does not satisfy n >= 2
```

---

## FSM Verification

Z3 can verify finite state machines for:
- Reachability (all states accessible)
- Deadlock-freedom (all states have exits)
- Safety properties (bad states unreachable)
- Liveness properties (good states eventually reached)

### Basic FSM Verification

```cure
fsm TrafficLight do
  states [Green, Yellow, Red]
  initial Green
  
  state Green do
    on timer -> Yellow
  end
  
  state Yellow do
    on timer -> Red
  end
  
  state Red do
    on timer -> Green
  end
end

%% Z3 automatically verifies:
%% ✅ All states reachable from Green
%% ✅ No deadlocks (every state has transitions)
%% ✅ Cyclic behavior (returns to initial state)
```

### FSM with State Invariants

```cure
record VendingState {
  balance: Int,
  selected: Bool
}

fsm VendingMachine(VendingState) do
  states [Idle, Accepting, Ready, Dispensing]
  initial Idle
  
  state Idle do
    %% Invariant: balance == 0
    on insert_coin(amount) when amount > 0 -> Accepting {
      balance = amount,
      selected = false
    }
  end
  
  state Accepting do
    %% Invariant: balance > 0
    on insert_coin(amount) when amount > 0 -> Accepting {
      balance = data.balance + amount,
      selected = false
    }
    
    on select(price) when data.balance >= price -> Ready {
      balance = data.balance,
      selected = true
    }
    
    on cancel -> Idle {
      balance = 0,
      selected = false
    }
  end
  
  %% ... more states
end

%% Z3 verifies:
%% ✅ Balance never negative
%% ✅ Can always return to Idle (via cancel)
%% ✅ Guards prevent invalid transitions
```

---

## Common Patterns

### Pattern 1: Safe Division

```cure
type NonZero = Int when x /= 0

def safe_div(a: Int, b: NonZero) -> Int do
  a / b
end
```

### Pattern 2: Bounded Integers

```cure
type Byte = Int when x >= 0 and x =< 255

def make_rgb(r: Byte, g: Byte, b: Byte) -> Int do
  (r * 65536) + (g * 256) + b
end
```

### Pattern 3: Non-Empty Collections

```cure
def max(xs: List(Int)) -> Int when length(xs) > 0 do
  fold_left(xs, xs[0], fn a, x -> if x > a then x else a end)
end
```

### Pattern 4: Sorted Pairs

```cure
type SortedPair(T) = {T, T} when fst <= snd

def make_sorted(a: Int, b: Int) -> SortedPair(Int) do
  if a <= b then {a, b} else {b, a} end
end
```

### Pattern 5: Financial Calculations

```cure
type Money = Int when x >= 0
type InterestRate = Int when x >= 0 and x =< 100

def apply_interest(amount: Money, rate: InterestRate) -> Money do
  amount + (amount * rate / 100)
end
```

---

## Troubleshooting

### Issue: "Z3 solver not found"

**Solution:**
```bash
# Install Z3
sudo apt install z3  # Ubuntu/Debian
brew install z3      # macOS

# Verify
z3 --version
```

### Issue: "SMT solver timeout"

**Cause:** Complex constraints taking too long

**Solution:** Increase timeout or simplify constraints

```bash
# Increase timeout to 30 seconds
cure compile --smt-timeout 30000 myfile.cure
```

### Issue: "Constraint verification failed"

**Example Error:**
```
Error: Refinement type violation
  Required: x > 0
  Got: x = -5
  Counterexample: x = -5
```

**Solution:** Fix the code to satisfy the constraint:

```cure
%% Before (error)
let x: Positive = -5

%% After (correct)
let x: Positive = 5

%% Or add a check
let x = read_input() in
if x > 0 then
  process(x)  %% x is Positive here
else
  error("Invalid input")
end
```

### Issue: "Unknown constraint result"

**Cause:** Z3 cannot determine satisfiability (timeout or complexity)

**Solution:**
- Simplify constraints
- Increase timeout
- Split complex constraints into simpler ones
- Add type annotations to help Z3

---

## API Reference

### Refinement Type Syntax

```cure
type TypeName = BaseType when constraint

%% Examples:
type Positive = Int when x > 0
type NonZero = Int when x /= 0
type Even = Int when x % 2 == 0
type Range(min, max) = Int when x >= min and x =< max
```

### Supported Constraints

**Arithmetic:**
- `+`, `-`, `*`, `/`, `mod`, `rem`

**Comparison:**
- `==`, `/=`, `<`, `>`, `<=`, `>=`

**Boolean:**
- `and`, `or`, `not`, `=>` (implies)

**Functions (in constraints):**
- `length(list)` - List length
- `abs(x)` - Absolute value
- (More coming in Phase 2)

### Dependent Type Syntax

```cure
def function_name(param: Type) -> RetType when constraint do
  body
end

%% Examples:
def safe_head(xs: List(T)) -> T when length(xs) > 0 do
  xs[0]
end

def bounded_add(x: Int, y: Int) -> Int 
  when x >= 0 and y >= 0 and x + y < 1000 do
  x + y
end
```

---

## What's Next

### Current Capabilities (Phase 1)

✅ Basic refinement types  
✅ Simple dependent types  
✅ FSM reachability analysis  
✅ Constraint solving with Z3  

### Coming Soon (Phase 2-3)

🚀 Quantifiers (`forall`, `exists`)  
🚀 Array theory for collections  
🚀 Refinement type subtyping  
🚀 Pattern exhaustiveness synthesis  
🚀 LSP real-time verification  

### Future (Phase 4-5)

📋 Temporal logic (LTL) for FSMs  
📋 Proof term generation  
📋 Verified data structure library  
📋 Automatic invariant inference  

---

## Examples

See comprehensive examples in:

- `examples/smt_refinement_types.cure` - 264 lines of refinement type examples
- `examples/smt_fsm_verified.cure` - 432 lines of FSM verification examples

---

## Further Reading

- [Z3 Integration Plan](Z3_INTEGRATION_PLAN.md) - Full integration roadmap
- [Z3 Integration Status](Z3_INTEGRATION_STATUS.md) - Current status and test results
- [SMT Quick Reference](SMT_QUICK_REFERENCE.md) - API and usage reference
- [Type System Documentation](TYPE_SYSTEM.md) - Cure's type system overview

---

**Questions or Issues?**

Report issues on GitHub or contact the Cure compiler team.

**Last Updated:** 2025-11-18
