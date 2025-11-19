# SMT Integration Phases 4-6: Implementation Roadmap

**Date**: 2025-11-19  
**Status**: Planning → Implementation  
**Estimated Time**: 10-17 weeks total

---

## Overview

This document outlines the implementation plan for SMT Integration Phases 4-6, building on the completed Phases 1-3 foundation.

### Current Status (Baseline)
- ✅ Phase 1: Core SMT infrastructure (100%)
- ✅ Phase 2: Quantifiers & CLI configuration (100%)
- ✅ Phase 3: Refinement types & type integration (100%)
- 🟡 Phase 4: LSP integration (10% - framework exists)
- ⬜ Phase 5: Advanced features (0%)
- ⬜ Phase 6: Dependent types (0%)

---

## Phase 4: LSP Real-Time Verification

**Goal**: Enable real-time constraint verification in editors with rich diagnostics and code actions.

**Estimated Time**: 2-3 weeks  
**Current Progress**: 10%

### 4.1 Incremental Constraint Solving

**Objective**: Cache SMT results to avoid redundant verification  
**Files**: `lsp/cure_lsp_smt.erl`  
**Time**: 3-4 days

**Implementation Tasks**:
1. ✅ Verification state record exists (already implemented)
2. ❌ Implement persistent solver session
   - Keep Z3 process alive between verification runs
   - Use `(push)` and `(pop)` commands for scope management
   - Benefit: Avoid 50ms startup overhead per verification

3. ❌ Implement incremental cache
   - Hash constraints for cache keys
   - Store results: `#{Hash => {sat|unsat|unknown, Timestamp}}`
   - Invalidate cache on document changes

4. ❌ Implement document change tracking
   - Track which lines changed
   - Only reverify constraints in changed regions
   - Reuse results for unchanged code

**API**:
```erlang
% Initialize persistent solver
{ok, State} = cure_lsp_smt:init_verification_state(),

% Verify with incremental solving
{ok, Diagnostics, NewState} = cure_lsp_smt:verify_document_incremental(Uri, State),

% Invalidate cache on edit
NewState2 = cure_lsp_smt:invalidate_cache_region(Uri, StartLine, EndLine, NewState).
```

**Success Metrics**:
- ✅ <100ms verification for unchanged documents
- ✅ <500ms for small edits (1-10 lines)
- ✅ Cache hit rate >80% for typical editing

---

### 4.2 Rich Diagnostics with Counterexamples

**Objective**: Provide detailed error messages with SMT counterexamples  
**Files**: `lsp/cure_lsp_smt.erl`, `src/types/cure_refinement_types.erl`  
**Time**: 3-4 days

**Implementation Tasks**:
1. ✅ Diagnostic conversion functions exist (partial)
2. ❌ Enhance counterexample formatting
   - Show concrete values that violate constraints
   - Format in human-readable way

3. ❌ Add constraint context
   - Show where constraint was defined
   - Show constraint in Cure syntax (not SMT-LIB)

4. ❌ Implement hover hints
   - Show refinement type when hovering over variable
   - Show inferred constraints

**Example Output**:
```
Error: Refinement type constraint violated
  Required: Positive (x > 0)
  Counterexample: x = -5 violates constraint
  Defined at: examples/test.cure:10:15
```

**API**:
```erlang
% Enhanced diagnostic with counterexample
Diagnostic = #{
    range => #{start => #{line => 10, character => 5}, ...},
    severity => 1,  % Error
    message => <<"Refinement violated: x = -5 does not satisfy x > 0">>,
    source => <<"Cure SMT">>,
    code => <<"refinement-violation">>,
    relatedInformation => [
        #{
            location => #{uri => ..., range => ...},
            message => <<"Constraint defined here: type Positive = Int when x > 0">>
        }
    ]
}.
```

---

### 4.3 Code Actions & Quick Fixes

**Objective**: Suggest fixes for constraint violations  
**Files**: `lsp/cure_lsp_smt.erl`  
**Time**: 2-3 days

**Implementation Tasks**:
1. ✅ Code action framework exists (stub)
2. ❌ Implement constraint relaxation suggestions
   - Suggest weaker constraints that would pass
   - Example: `x > 0` → `x >= 0`

3. ❌ Implement runtime check insertion
   - Offer to add `when x > 0` guard
   - Insert assertion: `assert x > 0`

4. ❌ Implement type annotation suggestions
   - Suggest refinement types based on usage
   - Auto-infer constraints from guards

**Quick Fix Examples**:

**Fix 1: Add Guard**:
```cure
% Before
def divide(a: Int, b: Int): Int = a / b

% After (quick fix applied)
def divide(a: Int, b: Int) when b /= 0: Int = a / b
```

**Fix 2: Relax Constraint**:
```cure
% Error: Cannot prove Percentage <: Positive
type Percentage = Int when x >= 0 and x <= 100

% Suggested fix: Use NonNegative instead
type NonNegative = Int when x >= 0
def use_percentage(p: NonNegative): Int = ...
```

**Fix 3: Add Runtime Check**:
```cure
def process(n: Int): Result =
    % Quick fix inserts this:
    if n > 0 then
        divide(100, n)
    else
        error("n must be positive")
    end
```

---

### 4.4 Performance Optimization

**Objective**: Ensure LSP remains responsive  
**Time**: 2-3 days

**Implementation Tasks**:
1. ❌ Implement query batching
   - Batch multiple constraints into single SMT query
   - Use `(assert ...)` multiple times before `(check-sat)`

2. ❌ Implement timeout tuning
   - Short timeout (500ms) for LSP
   - Long timeout (5000ms) for full compilation
   - Cancel verification on file close

3. ❌ Implement background verification
   - Queue verification tasks
   - Process in background worker
   - Return cached results immediately

4. ❌ Profile and optimize hot paths
   - Measure constraint extraction time
   - Optimize SMT-LIB generation
   - Cache parsed AST

**Performance Targets**:
- Constraint extraction: <50ms
- SMT query (simple): <100ms
- SMT query (complex): <500ms
- Full document verification: <1s

---

### 4.5 Testing & Documentation

**Time**: 2-3 days

**Tests to Create**:
1. LSP incremental solving test
2. Counterexample formatting test
3. Code action generation test
4. Performance benchmark test

**Documentation to Write**:
1. LSP SMT user guide
2. Configuration guide (timeout, solver selection)
3. Troubleshooting guide (Z3 not found, etc.)
4. Performance tuning guide

---

## Phase 5: Advanced Features

**Goal**: Add advanced SMT capabilities for pattern synthesis, optimization, and FSM verification.

**Estimated Time**: 4-6 weeks  
**Current Progress**: 0%

### 5.1 Array Theory Support

**Objective**: Enable list/vector constraints with SMT arrays  
**Files**: `src/smt/cure_smt_translator.erl`, new `src/smt/cure_smt_array.erl`  
**Time**: 1-2 weeks

**Implementation**:
1. Add array theory to SMT-LIB translation
   ```smt
   (declare-const arr (Array Int Int))
   (assert (forall ((i Int)) (=> (and (>= i 0) (< i n)) (> (select arr i) 0))))
   ```

2. Support list constraints:
   ```cure
   type AllPositive = List(Int) when forall i. 0 <= i < length(xs) => xs[i] > 0
   type Sorted = List(Int) when forall i j. i < j => xs[i] <= xs[j]
   ```

3. Implement array operations:
   - `select` (array indexing)
   - `store` (array update)
   - quantifiers over array indices

**Success Criteria**:
- ✅ Can express "all positive" list constraint
- ✅ Can prove sorted list properties
- ✅ 10+ array theory tests passing

---

### 5.2 Pattern Exhaustiveness Checking

**Objective**: Use SMT to prove pattern matching is exhaustive  
**Files**: `src/smt/cure_pattern_checker.erl` (exists), enhance with SMT  
**Time**: 1 week

**Current State**:
- Pattern checker exists
- Uses basic symbolic analysis
- **Enhancement**: Add SMT backend for complex patterns

**Implementation**:
1. Convert patterns to SMT constraints
   ```erlang
   Pattern: | 0 -> ... | n when n > 0 -> ...
   SMT: (assert (or (= x 0) (> x 0)))
   Check: (check-sat) with (assert (not (or ...)))
   ```

2. Prove exhaustiveness via SMT
   - Generate SMT query for "not covered"
   - If unsat → exhaustive
   - If sat → show missing pattern

3. Suggest missing patterns
   - Extract model from SAT result
   - Generate pattern from model
   - Format in Cure syntax

**Example**:
```cure
match x with
| 0 -> "zero"
| n when n > 0 -> "positive"
end
% SMT proves: Missing case for n < 0
% Suggested fix: Add | n when n < 0 -> ...
```

---

### 5.3 Guard Optimization

**Objective**: Eliminate redundant guards via SMT  
**Files**: New `src/smt/cure_guard_optimizer.erl`  
**Time**: 1 week

**Implementation**:
1. Detect redundant guards
   ```cure
   if n > 10 then
       if n > 5 then  % Redundant! n > 10 implies n > 5
           ...
       end
   end
   ```

2. Prove guard implications
   - Use `prove_implication(G1, G2, Env)`
   - If G1 → G2, remove G2

3. Optimize guard ordering
   - Order guards by specificity
   - More restrictive guards first

**Benefits**:
- Faster runtime (fewer checks)
- Clearer code (no redundant conditions)
- Compiler warnings for dead code

---

### 5.4 FSM Verification via SMT

**Objective**: Verify FSM properties using SMT  
**Files**: Enhance `src/fsm/cure_fsm_verifier.erl`  
**Time**: 2 weeks

**Implementation**:
1. FSM state invariants
   ```cure
   fsm BankAccount do
       payload: {balance: Int}
       invariant: balance >= 0  % Verify via SMT
       
       state Active do
           on withdraw(amount) when amount <= balance ->
               Active { balance = balance - amount }
       end
   end
   ```

2. Deadlock detection via SMT
   - Encode state graph as SMT constraints
   - Prove: ∀ states. ∃ transition

3. Reachability analysis
   - Prove all states reachable from initial
   - Generate counter-example path if not

4. Liveness properties
   - Eventually reach accepting state
   - No infinite loops in bad states

**Success Criteria**:
- ✅ Verify balance >= 0 invariant holds
- ✅ Detect deadlocks in FSM definitions
- ✅ Prove reachability properties
- ✅ 15+ FSM verification tests passing

---

## Phase 6: Dependent Type Constraints

**Goal**: Full dependent types with length-indexed vectors and verified arithmetic.

**Estimated Time**: 4-8 weeks  
**Current Progress**: 0%  
**Status**: Research phase - significant type system changes required

### 6.1 Design Dependent Type System

**Objective**: Architect dependent types compatible with existing system  
**Time**: 1-2 weeks

**Design Questions**:
1. Syntax for dependent types
   ```cure
   type Vector(T, n: Nat) = List(T) when length(this) == n
   
   def concat<T, m: Nat, n: Nat>(
       v1: Vector(T, m),
       v2: Vector(T, n)
   ): Vector(T, m + n) = v1 ++ v2
   ```

2. Type-level computation
   - How to handle `m + n` at type level?
   - SMT for proving `length(v1 ++ v2) == length(v1) + length(v2)`

3. Integration with refinement types
   - Dependent types as special refinement types?
   - Or separate type system layer?

**Deliverables**:
- Architecture document
- Grammar additions
- Type inference algorithm
- SMT encoding strategy

---

### 6.2 Parser & AST Support

**Objective**: Add syntax for dependent types  
**Files**: `src/parser/cure_parser.erl`, `src/parser/cure_ast.hrl`  
**Time**: 1 week

**Changes Needed**:
1. Type-level parameters
   ```cure
   type Vector(T, n: Nat) = ...
   ```

2. Dependent function types
   ```cure
   def safe_index<T, n: Nat>(v: Vector(T, n), i: Nat where i < n): T
   ```

3. Type-level expressions
   - Arithmetic: `m + n`, `m * n`
   - Comparisons: `n > 0`, `m >= n`

**AST Records**:
```erlang
-record(dependent_function_type, {
    type_params,    % [(Name, Kind, Constraint)]
    params,         % [#param{}]
    return_type,
    location
}).

-record(length_constraint, {
    var,            % Variable name
    length_expr,    % Length expression
    location
}).
```

---

### 6.3 Type Checking with SMT

**Objective**: Verify dependent type constraints  
**Files**: `src/types/cure_typechecker.erl`, new `src/types/cure_dependent_types.erl`  
**Time**: 2-3 weeks

**Implementation**:
1. Track type-level variables
   ```erlang
   % Environment now includes type-level vars
   Env = #{
       term_vars => #{x => int, ...},
       type_vars => #{n => nat, m => nat}
   }
   ```

2. Generate verification conditions
   ```cure
   def concat(v1: Vector(T, m), v2: Vector(T, n)): Vector(T, m+n) =
       v1 ++ v2
   
   % VC: length(v1 ++ v2) == m + n
   % Requires: length(v1) == m, length(v2) == n (from types)
   % Prove: length(v1 ++ v2) == length(v1) + length(v2)
   ```

3. Verify via SMT
   - Encode length axioms
   - Prove verification conditions
   - Report counterexamples

**Challenges**:
- List length not directly supported in SMT
- Need axioms: `length([]) = 0`, `length(x:xs) = 1 + length(xs)`
- Array theory may help

---

### 6.4 Standard Library Integration

**Objective**: Add dependent types to standard library  
**Files**: `lib/std/list.cure`, `lib/std/vector.cure` (new)  
**Time**: 1-2 weeks

**Dependent Types to Add**:
```cure
module Vector do
    type Vector(T, n: Nat) = List(T) when length(this) == n
    
    def empty<T>(): Vector(T, 0) = []
    
    def cons<T, n: Nat>(x: T, v: Vector(T, n)): Vector(T, n+1) =
        [x | v]
    
    def head<T, n: Nat>(v: Vector(T, n+1)): T =
        match v with
        | [x | _] -> x
        end
    
    def tail<T, n: Nat>(v: Vector(T, n+1)): Vector(T, n) =
        match v with
        | [_ | xs] -> xs
        end
    
    def concat<T, m: Nat, n: Nat>(
        v1: Vector(T, m),
        v2: Vector(T, n)
    ): Vector(T, m+n) =
        v1 ++ v2
    
    def take<T, n: Nat, k: Nat where k <= n>(
        v: Vector(T, n),
        k: Nat
    ): Vector(T, k) =
        ...
end
```

**Benefits**:
- No runtime bounds checks needed
- Prove safety at compile time
- Better optimization opportunities

---

## Timeline Summary

| Phase | Feature | Time | Start | End |
|-------|---------|------|-------|-----|
| 4.1 | Incremental solving | 3-4 days | Week 1 | Week 1 |
| 4.2 | Rich diagnostics | 3-4 days | Week 1 | Week 2 |
| 4.3 | Code actions | 2-3 days | Week 2 | Week 2 |
| 4.4 | Performance | 2-3 days | Week 2 | Week 3 |
| 4.5 | Testing & docs | 2-3 days | Week 3 | Week 3 |
| **Phase 4 Total** | **LSP Integration** | **2-3 weeks** | | |
| 5.1 | Array theory | 1-2 weeks | Week 4 | Week 5-6 |
| 5.2 | Pattern checking | 1 week | Week 6 | Week 7 |
| 5.3 | Guard optimization | 1 week | Week 7 | Week 8 |
| 5.4 | FSM verification | 2 weeks | Week 8 | Week 10 |
| **Phase 5 Total** | **Advanced Features** | **4-6 weeks** | | |
| 6.1 | Design | 1-2 weeks | Week 11 | Week 12-13 |
| 6.2 | Parser support | 1 week | Week 13 | Week 14 |
| 6.3 | Type checking | 2-3 weeks | Week 14 | Week 16-17 |
| 6.4 | Standard library | 1-2 weeks | Week 17 | Week 18-19 |
| **Phase 6 Total** | **Dependent Types** | **4-8 weeks** | | |

**Total Estimated Time**: 10-17 weeks

---

## Success Criteria

### Phase 4
- ✅ LSP responds in <100ms for cached results
- ✅ Counterexamples shown in diagnostics
- ✅ 5+ code action quick fixes implemented
- ✅ 20+ LSP integration tests passing

### Phase 5
- ✅ Array theory constraints supported
- ✅ Pattern exhaustiveness proven by SMT
- ✅ Redundant guards eliminated
- ✅ FSM invariants verified
- ✅ 50+ advanced feature tests passing

### Phase 6
- ✅ Dependent function types type-check
- ✅ Vector operations proven safe
- ✅ Standard library uses dependent types
- ✅ 30+ dependent type tests passing

---

## Risks & Mitigation

### Risk 1: SMT Solver Performance
**Impact**: LSP too slow for real-time use  
**Mitigation**:
- Implement aggressive caching
- Use short timeouts (500ms)
- Fall back to symbolic evaluation
- Profile and optimize hot paths

### Risk 2: Dependent Types Complexity
**Impact**: Type system becomes too complex  
**Mitigation**:
- Start with simple cases (Vector length)
- Incremental implementation
- Extensive testing
- User feedback before full deployment

### Risk 3: Z3 Availability
**Impact**: Users don't have Z3 installed  
**Mitigation**:
- Graceful fallback to symbolic evaluation
- Clear installation instructions
- Bundle Z3 with compiler (optional)
- Support multiple solvers (CVC5 backup)

---

**Next Steps**: Begin Phase 4.1 implementation (incremental solving)
