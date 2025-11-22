# Guard Implementation Status Report

## Current Implementation Analysis (2025-11-22)

### Overview
Cure has partial guard support. Guards work well in pattern matching contexts (match clauses, FSM transitions) but function-level guards need enhancement for full Erlang-style multi-clause functions.

---

## ✅ Fully Implemented Features

### 1. **Match Clause Guards**
**Status:** ✅ Complete  
**Files:** `cure_parser.erl`, `cure_guard_compiler.erl`, `cure_codegen.erl`

Guards in match expressions work perfectly:

```cure
def classify_age(age: Int): String =
  match age do
    x when x < 0 -> "Invalid age"
    x when x >= 0 and x < 13 -> "Child"
    x when x >= 13 and x < 20 -> "Teenager"
    x when x >= 20 -> "Adult"
  end
```

**Implementation:**
- Parser: `parse_match_clause/1` handles `when` keyword
- AST: `#match_clause{pattern, guard, body, location}`
- Compiler: `cure_guard_compiler:compile_guard/2` generates BEAM instructions
- Full support for comparison, boolean logic, arithmetic, type checks

### 2. **FSM Transition Guards**
**Status:** ✅ Complete  
**Files:** `cure_parser.erl`, `cure_fsm_runtime.erl`

Guards in FSM state transitions work correctly:

```cure
fsm TrafficLight do
  states = [Red, Yellow, Green]
  initial = Red
  
  state Red do
    event(tick) when count > 10 -> Green
  end
end
```

**Implementation:**
- Parser: Handles `when` in FSM transitions
- AST: `#transition{event, guard, target, action, location}`
- Runtime: Guard evaluation integrated into FSM event handling

### 3. **Refinement Type Guards**
**Status:** ✅ Complete  
**Files:** `cure_refinement_types.erl`, `cure_smt_translator.erl`

Type-level constraints using guards:

```cure
type Positive = Int when x > 0
type NonZero = Int when x /= 0
type Percentage = Int when x >= 0 and x <= 100
```

**Implementation:**
- SMT integration for verification
- Subtyping relationships proven by Z3
- Used in function signatures for compile-time checking

### 4. **Guard Safety Analysis**
**Status:** ✅ Complete  
**File:** `cure_guard_compiler.erl`

**Features:**
- `is_guard_safe/1` - Validates guard expressions
- Only allows safe BIFs (no side effects)
- Supported operations:
  - Arithmetic: `+, -, *, /, div, rem`
  - Comparison: `==, !=, <, >, <=, >=`
  - Boolean: `and, or, not, andalso, orelse`
  - Type checks: `is_integer, is_float, is_atom, is_list`, etc.
  - List/Tuple: `hd, tl, length, element`

### 5. **Guard Optimization**
**Status:** ✅ Complete  
**File:** `cure_guard_compiler.erl`

**Optimizations:**
- Constant folding: `5 + 3` → `8`
- Boolean simplification: `true andalso X` → `X`
- Dead code elimination: `false andalso _` → `false`

---

## ⚠️ Partially Implemented Features

### 1. **Function-Level Guards (Single Clause)**
**Status:** ⚠️ Partial - Parser works, codegen needs enhancement  
**Files:** `cure_parser.erl` (lines 745-774), `cure_codegen.erl`

**Current syntax support:**
```cure
def array_get(arr: List(Int), idx: Index) -> Option(Int)
  when idx >= 0 and idx < length(arr) 
do
  list_nth(arr, idx)
end
```

**Parser implementation:**
- ✅ Parses `when GUARD` after return type
- ✅ Stores in `#function_def{constraint = Guard}`
- ✅ Supports both `when ... -> Type` and `-> Type when ...` orderings

**Codegen issues:**
- ⚠️ Guard compilation exists but integration incomplete
- ⚠️ Runtime guard checking needs proper flow
- ⚠️ Error handling for failed guards not robust

---

## ❌ Missing Features

### 1. **Multi-Clause Functions with Guards**
**Status:** ❌ Not implemented  
**Target:** Erlang-style function definitions

**Desired syntax:**
```cure
def abs(x: Int): Int when x >= 0 = x
def abs(x: Int): Int when x < 0 = -x

def factorial(n: Int): Int when n == 0 = 1
def factorial(n: Int): Int when n > 0 = n * factorial(n - 1)
```

**Requirements:**
1. Parse multiple function definitions with same name
2. Group clauses by name/arity
3. Generate dispatch logic based on guards
4. Maintain clause order for evaluation
5. Handle overlapping guards (first match wins)

**Implementation needs:**
- Parser: Collect multiple clauses during module parsing
- AST: Already has `#function_def{clauses = [#function_clause{}]}`
- Codegen: Generate try-next-clause logic for failed guards
- Type system: Unify return types across clauses

### 2. **Guard Sequences (Comma Operator)**
**Status:** ❌ Not implemented

**Erlang syntax:**
```erlang
when Guard1, Guard2, Guard3  %% All must be true (like 'and')
when Guard1; Guard2; Guard3  %% Any can be true (like 'or')
```

**Cure could support:**
```cure
def foo(x: Int) when x > 0, x < 100 = "valid"  %% both conditions
```

Currently must use: `when x > 0 and x < 100`

### 3. **Guard Context in Type Checking**
**Status:** ❌ Partial integration

**Need:**
- Use guard information for flow-sensitive typing
- Narrow types in function body based on guard
- Example: `when x > 0` → treat `x` as `Positive` in body

---

## 🏗️ Architecture Review

### AST Structure
```erlang
%% Function with single clause
#function_def{
  name = abs,
  type_params = [],
  clauses = [#function_clause{
    params = [#param{name = x, type = int_type}],
    return_type = int_type,
    constraint = Guard,  % The guard expression
    body = Body,
    location = Loc
  }],
  ...
}
```

**Status:** ✅ AST supports multi-clause (list of clauses)

### Parser Flow
```
parse_function(State) ->
  1. Parse: def name(params): ReturnType
  2. Parse: when Guard (optional)
  3. Parse: = Body or do...end
  4. Create #function_clause{constraint = Guard}
  5. Wrap in #function_def{clauses = [Clause]}
```

**Status:** ⚠️ Only creates single-clause functions

### Codegen Flow
```
compile_function(#function_def{clauses = Clauses}) ->
  For single clause:
    1. Compile parameters
    2. Compile guard (if present)
    3. Compile body
    4. Emit function code
    
  For multiple clauses: ❌ NOT IMPLEMENTED
    1. For each clause:
      a. Try pattern match
      b. Evaluate guard
      c. If success: execute body
      d. If fail: try next clause
    2. If all fail: error
```

### Type System Integration
```
check_function(#function_def{clauses = Clauses}) ->
  For each clause:
    1. Check parameter types
    2. ❌ Extract constraints from guard
    3. ❌ Use constraints for refinement typing in body
    4. Check body expression type
    5. Verify return type matches
    6. ❌ Unify return types across clauses
```

---

## 📊 Guard Support Matrix

| Feature | Match | FSM | Type | Function | Status |
|---------|-------|-----|------|----------|--------|
| Simple comparison (`x > 0`) | ✅ | ✅ | ✅ | ⚠️ | Works, needs testing |
| Boolean logic (`and`, `or`) | ✅ | ✅ | ✅ | ⚠️ | Works |
| Arithmetic (`x + y > z`) | ✅ | ✅ | ✅ | ⚠️ | Works |
| Type guards (`is_integer`) | ✅ | ✅ | ❌ | ⚠️ | Limited |
| Multiple clauses | N/A | N/A | N/A | ❌ | Missing |
| Guard sequences | ✅ | ⚠️ | ❌ | ❌ | Partial |
| Constant folding | ✅ | ✅ | ✅ | ✅ | Complete |
| Flow-sensitive typing | N/A | N/A | ❌ | ❌ | Missing |

---

## 🎯 Recommended Implementation Plan

### Phase 1: Complete Single-Clause Function Guards
1. ✅ Review existing codegen for function guards
2. ✅ Add runtime guard evaluation
3. ✅ Proper error messages for guard failures
4. ✅ Integration tests

### Phase 2: Multi-Clause Functions
1. Extend parser to collect multiple clauses
2. Modify module parser to group functions by name/arity
3. Update codegen for clause dispatch
4. Add clause ordering tests

### Phase 3: Type System Integration
1. Extract guard constraints for refinement typing
2. Flow-sensitive type narrowing in function bodies
3. Cross-clause return type unification
4. SMT integration for guard verification

### Phase 4: Advanced Features
1. Guard sequences (`,` and `;`)
2. Improved optimization
3. Better error messages
4. Performance tuning

---

## 📝 Test Coverage

### Existing Tests
- ✅ `guard_compilation_test.erl` - Guard compiler tests
- ✅ `guard_optimization_test.erl` - Optimization tests
- ✅ `04_pattern_guards.cure` - Match clause examples
- ✅ `fsm_guard_verification_demo.erl` - FSM guard tests

### Missing Tests
- ❌ Function-level single-clause guard tests
- ❌ Multi-clause function tests
- ❌ Guard failure error handling
- ❌ Integration with refinement types
- ❌ Performance benchmarks

---

## 🔍 Code Locations

### Parser
- **Main:** `src/parser/cure_parser.erl`
- **Function parsing:** Lines 666-842 (`parse_function/1`)
- **Guard parsing:** Lines 745-774 (when clause handling)
- **Match guards:** Lines 2116-2119, 2286-2290

### AST
- **Header:** `src/parser/cure_ast.hrl`
- **Function def:** Lines 28-49 (`#function_def`)
- **Function clause:** Lines 28-34 (`#function_clause`)
- **Match clause:** Lines 207-212 (`#match_clause`)
- **Transition:** Lines 108-115 (`#transition`)

### Codegen
- **Main:** `src/codegen/cure_codegen.erl`
- **Guard compiler:** `src/codegen/cure_guard_compiler.erl` (Complete module)
- **Function compilation:** Lines 2214+ (`compile_function`)

### Type System
- **Types:** `src/types/cure_types.erl`
- **Refinement:** `src/types/cure_refinement_types.erl`
- **Type checking:** `src/types/cure_typechecker.erl`

### Runtime
- **FSM:** `src/fsm/cure_fsm_runtime.erl`
- **Guard execution:** Integrated in FSM event handling

---

## 💡 Design Decisions

### Guard Semantics
Following Erlang/Elixir conventions:
1. Guards must be **pure** (no side effects)
2. Guards must be **safe** (no exceptions that crash)
3. Failed guard = clause doesn't match (not an error)
4. Evaluation order: **sequential**, first match wins

### Syntax Choices
```cure
% Preferred: guard after return type
def foo(x: Int): Int when x > 0 = x + 1

% Also supported: guard before return type  
def foo(x: Int) when x > 0 -> Int = x + 1

% Multi-clause (to be implemented)
def foo(x: Int): Int when x > 0 = x
def foo(x: Int): Int when x <= 0 = -x
```

### Integration with Refinement Types
Guards on functions should refine parameter types:
```cure
type Positive = Int when x > 0

def process(x: Int) when x > 0 = ...
  % Inside body, x should be treated as Positive
  % This enables more precise type checking
```

---

## 🚀 Next Steps

See the associated implementation tasks in the TODO list. Priority order:

1. **Document current state** ✅ (this document)
2. **Test and fix single-clause guards** - Ensure runtime works
3. **Implement multi-clause parsing** - Core feature
4. **Implement multi-clause codegen** - Core feature
5. **Type system integration** - Enhanced safety
6. **Comprehensive testing** - Ensure quality
7. **Documentation updates** - User-facing docs

---

## 📚 References

- **Erlang Guards:** https://www.erlang.org/doc/reference_manual/expressions.html#guards
- **Elixir Guards:** https://hexdocs.pm/elixir/guards.html
- **Existing examples:** `examples/04_pattern_guards.cure`
- **Test suite:** `test/guard_compilation_test.erl`
