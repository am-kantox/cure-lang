# Dependent Type System Design for Cure

**Version**: 1.0  
**Date**: 2025-11-19  
**Status**: Design Phase  
**Author**: SMT Integration Team

---

## Table of Contents

1. [Overview](#overview)
2. [Motivation](#motivation)
3. [Design Principles](#design-principles)
4. [Syntax](#syntax)
5. [Type System Architecture](#type-system-architecture)
6. [SMT Encoding Strategy](#smt-encoding-strategy)
7. [Type Inference](#type-inference)
8. [Integration with Existing System](#integration-with-existing-system)
9. [Implementation Plan](#implementation-plan)
10. [Examples](#examples)

---

## Overview

This document outlines the design of dependent types for the Cure programming language. Dependent types allow types to depend on values, enabling compile-time verification of properties like array bounds, list lengths, and numerical constraints.

### Goals

1. **Safety**: Eliminate runtime bounds checks through compile-time verification
2. **Expressiveness**: Enable precise specifications (e.g., `Vector(T, n)` with length `n`)
3. **SMT Integration**: Leverage existing SMT infrastructure for verification
4. **Backward Compatibility**: Maintain compatibility with existing type system
5. **Practicality**: Focus on useful cases (lengths, bounds) before full dependent types

### Non-Goals

1. Full dependent type theory (à la Coq/Agda) - too complex
2. Dependent pattern matching initially - add later if needed
3. Type-level computation beyond arithmetic - keep simple

---

## Motivation

### Problem: Array Bounds Checks

Current Cure code requires runtime checks:

```cure
def head(xs: List(Int)): Int =
    match xs with
    | [x | _] -> x
    | [] -> error("empty list")  % Runtime error!
    end
```

### Solution: Length-Indexed Types

With dependent types, prove safety at compile-time:

```cure
def head<T, n: Nat>(xs: Vector(T, n+1)): T =
    match xs with
    | [x | _] -> x
    end
    % No error case needed - type system proves xs is non-empty
```

### Benefits

- **No runtime checks**: Compiler proves safety
- **Better documentation**: Types express invariants
- **Optimization**: Compiler can optimize away checks
- **Error prevention**: Catch bugs at compile time

---

## Design Principles

### 1. Start Simple

Focus on **refinement-based dependent types**:
- Types parametrized by values (e.g., `Vector(T, n)`)
- Constraints verified by SMT
- No full type-level computation initially

### 2. Leverage Existing Infrastructure

- Build on refinement types (`cure_refinement_types.erl`)
- Use SMT for verification (`cure_smt_translator.erl`)
- Extend type checker, don't replace it

### 3. Gradual Typing

- Optional: Use dependent types only where needed
- Fallback: Regular types still work
- Mixed: Can combine dependent and non-dependent code

### 4. Practical Focus

Prioritize common use cases:
1. Length-indexed lists/vectors
2. Bounded integers (e.g., `0 ≤ x < n`)
3. Non-null types
4. FSM state invariants

---

## Syntax

### Type-Level Parameters

```cure
type Vector(T, n: Nat) = List(T) when length(this) == n
type BoundedInt(min: Int, max: Int) = Int when min <= this <= max
type Matrix(T, rows: Nat, cols: Nat) = Vector(Vector(T, cols), rows)
```

**Grammar Addition**:
```
type_def ::= 'type' identifier type_params '=' type_expr constraints
type_params ::= '(' param_list ')'
param_list ::= param | param ',' param_list
param ::= identifier ':' type  % Value parameter
        | identifier           % Type parameter
```

### Dependent Function Types

```cure
def concat<T, m: Nat, n: Nat>(
    v1: Vector(T, m),
    v2: Vector(T, n)
): Vector(T, m + n) =
    v1 ++ v2

def safe_index<T, n: Nat>(
    v: Vector(T, n),
    i: Nat where i < n
): T =
    nth(v, i)  % No bounds check needed!
```

**Grammar Addition**:
```
function_def ::= 'def' identifier type_params '(' param_list ')' type_annotation '=' expr
type_params ::= '<' type_param_list '>'
type_param ::= identifier                   % Type parameter
             | identifier ':' type_expr      % Value parameter with type
             | identifier ':' type 'where' expr  % Constrained value parameter
```

### Type-Level Expressions

Supported operations:
- **Arithmetic**: `m + n`, `m - n`, `m * n`, `m / n`
- **Comparison**: `m == n`, `m < n`, `m <= n`
- **Boolean**: `and`, `or`, `not`

```cure
type AddResult(m: Nat, n: Nat) = Int where this == m + n
type InRange(lo: Int, hi: Int) = Int where lo <= this <= hi
type NonEmpty(T) = Vector(T, n) where n > 0
```

### Constraint Propagation

```cure
def append<T, m: Nat, n: Nat>(
    v1: Vector(T, m),
    v2: Vector(T, n)
): Vector(T, m + n) =
    % Compiler must prove:
    %   length(v1) == m (from v1's type)
    %   length(v2) == n (from v2's type)
    %   length(v1 ++ v2) == m + n (return type requirement)
    v1 ++ v2
```

---

## Type System Architecture

### Type Representation

**AST Records** (`cure_ast.hrl`):

```erlang
%% Dependent type with value parameters
-record(dependent_type, {
    name,           % Type constructor name (e.g., 'Vector')
    type_params,    % Type parameters [T, U, ...]
    value_params,   % Value parameters [{n, nat}, {m, nat}, ...]
    constraints,    % Refinement constraints [expr()]
    location
}).

%% Dependent function type
-record(dependent_function_type, {
    type_params,    % Type-level parameters [{T, kind}, {n, nat}, ...]
    params,         % Function parameters [#param{}]
    return_type,    % Return type (may depend on value params)
    constraints,    % Where clauses [expr()]
    location
}).

%% Type-level expression
-record(type_level_expr, {
    op,             % +, -, *, /, ==, <, <=, etc.
    operands,       % [expr() | identifier]
    location
}).
```

### Type Environment

Extended to track type-level variables:

```erlang
-record(type_env, {
    term_vars,      % #{VarName => Type} - term-level variables
    type_vars,      % #{TVar => Kind} - type variables (T, U, etc.)
    value_params,   % #{Param => Type} - value parameters (n: Nat, etc.)
    constraints,    % [Constraint] - accumulated constraints
    smt_env         % SMT environment for verification
}).
```

### Type Checking Phases

1. **Parsing**: Recognize dependent type syntax
2. **Elaboration**: Convert to internal representation
3. **Constraint Generation**: Extract verification conditions
4. **SMT Verification**: Prove constraints via Z3
5. **Error Reporting**: Show counterexamples if verification fails

---

## SMT Encoding Strategy

### Encoding Length Constraints

**Cure Code**:
```cure
type Vector(T, n: Nat) = List(T) when length(this) == n
```

**SMT Encoding**:
```smt
(declare-sort T)
(declare-sort List)
(declare-fun length (List) Int)

; Axioms for length
(assert (= (length nil) 0))
(assert (forall ((x T) (xs List))
    (= (length (cons x xs)) (+ 1 (length xs)))))

; Constraint for Vector(T, n)
(declare-const v List)
(declare-const n Int)
(assert (>= n 0))  ; n is Nat
(assert (= (length v) n))
```

### Encoding Arithmetic

**Cure Code**:
```cure
def concat<T, m: Nat, n: Nat>(
    v1: Vector(T, m),
    v2: Vector(T, n)
): Vector(T, m + n)
```

**Verification Condition**:
```
Given:
  length(v1) == m
  length(v2) == n
Prove:
  length(v1 ++ v2) == m + n
```

**SMT Query**:
```smt
(declare-const v1 List)
(declare-const v2 List)
(declare-const m Int)
(declare-const n Int)

; Given
(assert (>= m 0))
(assert (>= n 0))
(assert (= (length v1) m))
(assert (= (length v2) n))

; Append axiom
(assert (forall ((xs List) (ys List))
    (= (length (append xs ys)) (+ (length xs) (length ys)))))

; Prove: length(append v1 v2) == m + n
(assert (not (= (length (append v1 v2)) (+ m n))))
(check-sat)
; Expected: unsat (proof succeeds)
```

### Encoding Bounds

**Cure Code**:
```cure
def safe_index<T, n: Nat>(v: Vector(T, n), i: Nat where i < n): T
```

**Verification Condition**:
```
Given:
  length(v) == n
  i < n
  i >= 0
Prove:
  0 <= i < length(v)  (safe indexing)
```

**SMT Query**:
```smt
(declare-const n Int)
(declare-const i Int)

(assert (>= n 0))
(assert (>= i 0))
(assert (< i n))

; Prove: i is valid index
(assert (not (and (>= i 0) (< i n))))
(check-sat)
; Expected: unsat (proof succeeds)
```

---

## Type Inference

### Inference Rules

#### Rule 1: Length Propagation

```
Γ ⊢ e : List(T)    length(e) = n
─────────────────────────────────
Γ ⊢ e : Vector(T, n)
```

#### Rule 2: Arithmetic Inference

```
Γ ⊢ v1 : Vector(T, m)    Γ ⊢ v2 : Vector(T, n)
──────────────────────────────────────────────
Γ ⊢ v1 ++ v2 : Vector(T, m + n)
```

#### Rule 3: Constraint Propagation

```
Γ ⊢ e : τ where φ    Γ ⊢ φ ⇒ ψ (via SMT)
────────────────────────────────────────
Γ ⊢ e : τ where ψ
```

### Inference Algorithm

```erlang
infer_dependent_type(Expr, Env) ->
    % 1. Infer base type
    {BaseType, Constraints1} = infer_type(Expr, Env),
    
    % 2. Extract value-level information
    ValueInfo = extract_value_info(Expr, Env),
    
    % 3. Generate dependent type
    DepType = case {BaseType, ValueInfo} of
        {{list, ElemType}, {length, N}} ->
            #dependent_type{name = 'Vector', type_params = [ElemType], value_params = [{n, N}]};
        _ ->
            BaseType
    end,
    
    % 4. Generate verification conditions
    VCs = generate_verification_conditions(Expr, DepType, Env),
    
    % 5. Verify via SMT
    case verify_constraints(VCs, Env) of
        {ok, _} -> {DepType, Constraints1 ++ VCs};
        {error, Reason} -> {error, Reason}
    end.
```

---

## Integration with Existing System

### Phase 1: Extend Refinement Types

Dependent types as special refinement types:

```erlang
% Current refinement type
#refinement_type{
    base_type = {primitive, int},
    predicate = #binary_op_expr{op = '>', left = #identifier_expr{name = x}, right = #literal_expr{value = 0}}
}

% Extended for dependent types
#dependent_refinement_type{
    base_type = {list, T},
    value_params = [{n, {primitive, nat}}],
    predicate = #binary_op_expr{
        op = '==',
        left = #function_call_expr{function = length, args = [this]},
        right = #identifier_expr{name = n}
    }
}
```

### Phase 2: Type Checker Integration

Extend `cure_typechecker.erl`:

```erlang
% Add to type checking
check_expr(#function_call_expr{function = F, args = Args}, ExpectedType, Env) ->
    FType = lookup_function_type(F, Env),
    
    % Check if dependent function
    case FType of
        #dependent_function_type{} ->
            check_dependent_application(F, Args, FType, ExpectedType, Env);
        _ ->
            check_regular_application(F, Args, FType, ExpectedType, Env)
    end.

check_dependent_application(F, Args, FType, ExpectedType, Env) ->
    % 1. Infer argument types and extract values
    {ArgTypes, ArgValues} = lists:unzip([infer_arg(A, Env) || A <- Args]),
    
    % 2. Instantiate dependent type with concrete values
    InstantiatedType = instantiate_dependent_type(FType, ArgValues),
    
    % 3. Check subtyping with SMT
    check_subtype_smt(InstantiatedType, ExpectedType, Env).
```

### Phase 3: SMT Translator Extension

Extend `cure_smt_translator.erl`:

```erlang
% Add dependent type translation
translate_type(#dependent_type{name = 'Vector', type_params = [T], value_params = [{n, _}]}, Env) ->
    TElemSort = translate_type(T, Env),
    [
        "(declare-sort ", atom_to_list(TElemSort), ")\n",
        "(declare-fun length (List) Int)\n",
        "(assert (= (length vec) ", translate_expr(n, Env), "))\n"
    ].
```

---

## Implementation Plan

### Phase 6.1: Design (Current)
- ✅ Design document
- ✅ Syntax specification
- ✅ Type system architecture
- ✅ SMT encoding strategy

### Phase 6.2: Parser Support (Week 13)
- Add dependent type syntax to lexer
- Extend parser for value parameters
- Create AST records
- Unit tests for parsing

### Phase 6.3: Type Checking (Weeks 14-16)
- Extend type environment
- Implement constraint generation
- Add SMT verification
- Error reporting with counterexamples

### Phase 6.4: Standard Library (Weeks 17-18)
- Implement `Vector` module
- Add dependent types to `List` operations
- Create examples and documentation

---

## Examples

### Example 1: Safe Head

```cure
% Current: Runtime error possible
def head(xs: List(Int)): Int =
    match xs with
    | [x | _] -> x
    | [] -> error("empty list")
    end

% With dependent types: Compile-time safety
def head<T, n: Nat>(xs: Vector(T, n+1)): T =
    match xs with
    | [x | _] -> x
    end
    % Type system proves xs is non-empty (n+1 >= 1)
```

### Example 2: Matrix Operations

```cure
type Matrix(T, rows: Nat, cols: Nat) = Vector(Vector(T, cols), rows)

def transpose<T, m: Nat, n: Nat>(
    matrix: Matrix(T, m, n)
): Matrix(T, n, m) =
    % Compiler verifies dimensions are correct
    ...

def multiply<T, m: Nat, n: Nat, p: Nat>(
    a: Matrix(T, m, n),
    b: Matrix(T, n, p)
): Matrix(T, m, p) =
    % Compiler checks: a.cols == b.rows
    ...
```

### Example 3: Bounded Integers

```cure
type Percentage = Int where 0 <= this <= 100
type Index(n: Nat) = Int where 0 <= this < n

def get_percentage(value: Int, total: Int where total > 0): Percentage =
    (value * 100) / total  % Compiler proves result is in [0, 100]

def safe_nth<T, n: Nat>(xs: Vector(T, n), i: Index(n)): T =
    nth(xs, i)  % No bounds check needed!
```

### Example 4: FSM with Invariants

```cure
fsm BankAccount do
    type Balance = Int where this >= 0
    
    payload: {balance: Balance}
    
    state Active(balance: Balance) do
        on deposit(amount: Int where amount > 0) ->
            Active { balance = balance + amount }
            % Compiler proves: balance + amount >= 0
        
        on withdraw(amount: Int where amount <= balance) ->
            Active { balance = balance - amount }
            % Compiler proves: balance - amount >= 0
    end
end
```

---

## Open Questions

### Q1: Type-Level Computation

How much computation do we allow at the type level?

**Options**:
1. **Limited** (current design): Only arithmetic and comparisons
2. **Extended**: Allow arbitrary pure functions
3. **Full**: Full dependent types with proof terms

**Decision**: Start with Limited (Option 1), extend if needed.

### Q2: Inference vs. Annotation

How much type inference should we provide?

**Options**:
1. **Explicit**: All dependent types must be annotated
2. **Partial**: Infer some cases (e.g., list append)
3. **Full**: Infer all dependent types

**Decision**: Start with Partial (Option 2) - infer simple cases, require annotations for complex ones.

### Q3: Subtyping

How do dependent types interact with subtyping?

```cure
% Is Vector(Int, 5) a subtype of Vector(Int, n) where n >= 5?
% Or Vector(Int, n) where n > 0?
```

**Decision**: Use SMT to check subtyping constraints case-by-case.

---

## Success Criteria

- ✅ Can express length-indexed vectors
- ✅ Compiler proves array bounds safety
- ✅ Can implement safe `head`, `tail`, `nth` operations
- ✅ Matrix dimensions verified at compile time
- ✅ 30+ dependent type tests passing
- ✅ Performance: <1s verification for typical functions
- ✅ Documentation and examples complete

---

## References

1. **Liquid Types**: Refinement types for Haskell (LiquidHaskell)
2. **Dependent Types**: Full dependent types (Agda, Idris, Coq)
3. **Hybrid Types**: Combining refinement and dependent types (F*)
4. **SMT-based Verification**: Using Z3 for type checking

---

**Next Steps**: Begin Phase 6.2 (Parser Support)
