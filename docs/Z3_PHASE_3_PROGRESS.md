# Z3 Integration - Phase 3: Type System Integration (In Progress)

## Executive Summary

Phase 3 focuses on deep integration of Z3 SMT solving into Cure's type system to enable refinement types, dependent type constraint checking, and automatic subtype verification.

## Current Status

### ✅ Completed Work

1. **Refinement Types Module Created** (`src/types/cure_refinement_types.erl`, 463 LOC)
   - Refinement type data structure: base type + variable + predicate + location
   - Subtyping verification framework using SMT
   - Constraint checking for values against refinement predicates
   - Precondition/postcondition verification
   - Constraint propagation infrastructure
   - Error formatting and counterexample generation
   
2. **Test Suite Created** (`test/refinement_types_test.erl`, 357 LOC)
   - 20 comprehensive test cases:
     * 3 refinement type creation tests (PASSING)
     * 4 subtyping tests (1 timed out, needs optimization)
     * 5 constraint checking tests
     * 2 precondition verification tests
     * 3 constraint propagation tests
     * 2 error formatting tests
     * 2 integration tests

3. **Example Code Created** (`examples/refinement_types_advanced.cure`, 356 LOC)
   - Safe division with NonZero divisor
   - Array indexing with bounds checking
   - Financial calculations with constraints
   - Temperature conversions with physical constraints
   - Sorted list invariants
   - Network protocol state constraints (TCP)
   - Smart contract Wei amount tracking
   - Database pagination with size limits
   - Cryptographic key size validation
   - Matrix dimension compatibility

###  Issues Encountered

#### SMT Solver Performance
The internal DPLL-based SMT solver in `cure_smt_solver` is experiencing performance issues:
- Subtyping proofs timing out (e.g., proving `Positive <: NonZero`)
- Case splitting in DPLL solver getting stuck in infinite loops
- Need to switch to Z3 process integration (Phase 1-2) for complex proofs

**Root Cause**: The internal solver uses a simple DPLL algorithm that doesn't handle quantified formulas or implications efficiently. For refinement type subtyping `∀x. P(x) => Q(x)`, this requires Z3's more advanced proof capabilities.

**Solution**: Update refinement types module to use the Z3 process integration from Phase 1-2:
- Use `cure_smt_translator` to convert Cure AST to SMT-LIB format
- Send queries directly to Z3 via `cure_smt_process`
- Parse Z3 responses with `cure_smt_parser`

#### API Mismatch
Some expected functions weren't exported:
- `check_satisfiable/2` → Actually `check_satisfiable/1` (single constraint)
- `prove_constraint/3` → Actually `prove_constraint/2` (assumptions + goal)
- `expression_term/2` → Doesn't exist, use `addition_expression/1`, `subtraction_expression/1`, etc.

**Status**: Fixed in refinement types module.

## Architecture

### Refinement Type Representation

```erlang
-record(refinement_type, {
    base_type :: type_expr(),      % Int, Real, Bool, etc.
    variable :: atom(),            % x, y, z (refinement variable)
    predicate :: expr(),           % x > 0, x /= 0, etc.
    location :: location()
}).
```

### Subtyping Verification Process

```
1. Check base type compatibility (Positive: Int, NonZero: Int ✓)
2. Normalize predicates (rename variables for consistency)
3. Build implication: Pred1 => Pred2
4. Convert to SMT-LIB format
5. Ask Z3 to prove: (assert (forall ((x Int)) (=> Pred1 Pred2)))
6. Check Z3 result: sat/unsat/unknown
```

### Current Workflow

```
Cure Source Code
  ↓
Type Checker (finds refinement type)
  ↓
Refinement Types Module
  ↓
cure_refinement_types:check_subtype(Type1, Type2, Env)
  ↓
expr_to_smt_constraint(Pred1), expr_to_smt_constraint(Pred2)
  ↓
cure_smt_solver:prove_constraint([Pred1], Pred2)
  ↓
[CURRENT BOTTLENECK: Internal DPLL solver times out]
  ↓
{proved, Proof} | {disproved, CounterEx} | unknown
```

### Target Workflow (Using Z3 Integration)

```
Cure Source Code
  ↓
Type Checker (finds refinement type)
  ↓
Refinement Types Module
  ↓
cure_refinement_types:check_subtype(Type1, Type2, Env)
  ↓
cure_smt_translator:translate_refinement_subtype(Pred1, Pred2, Var, BaseType)
  ↓
SMT-LIB Query: (assert (forall ((x Int)) (=> (> x 0) (not (= x 0)))))
  ↓
cure_smt_process:query(SmtLib)
  ↓
Z3 Process (external, fast)
  ↓
cure_smt_parser:parse_result(Z3Output)
  ↓
{proved, true} | {disproved, CounterExample} | {unknown}
```

## Next Steps

### Immediate (Critical for Phase 3 Completion)

1. **Switch to Z3 Process Integration**
   - Update `cure_refinement_types:verify_subtype_smt/3` to use Z3 directly
   - Add `translate_refinement_subtype/4` to `cure_smt_translator`
   - Bypass internal DPLL solver for refinement type proofs

2. **Fix Timeout Issues**
   - Set reasonable timeout (e.g., 5 seconds) for Z3 queries
   - Return `{ok, false}` on timeout (conservative)
   - Log timeout events for debugging

3. **Complete Test Suite**
   - Run all 20 tests successfully
   - Add performance benchmarks (target: <100ms per subtype check)
   - Test with complex refinement chains

### Short-term (Rest of Phase 3)

4. **Type Checker Integration**
   - Hook `cure_refinement_types` into `cure_typechecker:process_when_clause_constraint/3`
   - Automatically check refinement type assignments
   - Verify function call arguments against refinement preconditions

5. **Dependent Type Constraint Checking**
   - Verify dependent types at compile time (e.g., `Vector(T, n)` where `n > 0`)
   - Check array bounds: `xs[i]` requires `0 <= i < length(xs)`
   - Validate FSM state constraints

6. **Constraint Environment Management**
   - Track refinement constraints through control flow
   - Propagate constraints in if/match expressions
   - Generate proof obligations for each branch

### Documentation

7. **User Guide Updates**
   - Document refinement type syntax
   - Show subtyping rules and proofs
   - Provide debugging tips for failed proofs

8. **API Documentation**
   - Export key functions from `cure_refinement_types`
   - Add EDoc comments with examples
   - Integration guide for type checker

## Test Results

### Passing Tests (3/20, 15%)
- ✅ `create_positive_type_test`
- ✅ `create_nonzero_type_test`
- ✅ `create_percentage_type_test`

### Timeout/Failing Tests (17/20, 85%)
- ⏱️ `subtyping_positive_is_nonzero_test` (TIMEOUT - DPLL bottleneck)
- ⏱️ `subtyping_nonzero_not_positive_test` (TIMEOUT)
- ⏱️ `subtyping_percentage_is_nonnegative_test` (TIMEOUT)
- ⏱️ `subtyping_reflexive_test` (TIMEOUT)
- ❓ `check_constraint_*` tests (untested after timeout)
- ❓ `verify_precondition_*` tests (untested after timeout)
- ❓ `propagate_constraints_*` tests (untested after timeout)
- ❓ Integration tests (untested after timeout)

**Target**: 20/20 passing (100%) with Z3 integration

## Performance Goals

- **Subtype Check**: <100ms per check
- **Constraint Verification**: <50ms per constraint
- **Z3 Startup**: <50ms (cached process)
- **Complex Proof**: <500ms (with quantifiers)

## Code Metrics

| Component | Lines of Code | Status |
|-----------|---------------|--------|
| cure_refinement_types.erl | 463 | Complete (needs Z3 integration) |
| refinement_types_test.erl | 357 | Complete (blocked by timeouts) |
| refinement_types_advanced.cure | 356 | Complete (examples) |
| **Total** | **1,176** | **In Progress** |

## Integration Points

### With Existing Code

1. **cure_typechecker.erl** (lines 3249-3370)
   - Hook refinement type checking into when clause processing
   - Call `cure_refinement_types:check_constraint/3`

2. **cure_smt_translator.erl** (Phase 2 complete)
   - Add `translate_refinement_subtype/4` function
   - Generate SMT-LIB for `∀x. P(x) => Q(x)`

3. **cure_smt_process.erl** (Phase 1 complete)
   - Already working with Z3 process
   - No changes needed

4. **cure_types.erl** (lines 3852-3893)
   - Constraint solving infrastructure ready
   - Add refinement type environment tracking

## Risk Assessment

| Risk | Severity | Mitigation |
|------|----------|------------|
| Z3 process crashes | Medium | Restart process automatically, cache results |
| Z3 not installed | High | Check for Z3 in build/test, provide clear error |
| Slow Z3 queries | Medium | Implement timeout (5s), cache common proofs |
| Complex proofs fail | Low | Fall back to conservative typing |

## Timeline

- **Week 1**: Switch to Z3 integration, fix timeouts ← **WE ARE HERE**
- **Week 2**: Complete test suite, integrate with type checker
- **Week 3**: Constraint propagation, dependent types
- **Week 4**: Documentation, performance tuning

**Estimated Completion**: 3-4 weeks from now

## Conclusion

Phase 3 has made solid progress with the refinement types infrastructure in place. The main blocker is switching from the internal DPLL solver to Z3 process integration. Once this is done, all tests should pass quickly, and we can proceed with type checker integration and constraint propagation.

**Next Action**: Implement `translate_refinement_subtype/4` in `cure_smt_translator` and update `verify_subtype_smt/3` to use Z3 directly.