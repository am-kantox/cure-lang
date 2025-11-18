# Phase 3 Completion & Phase 5 Roadmap

**Date**: 2025-01-25  
**Status**: Planning Document  
**Priority**: High (Phase 3), Medium (Phase 5)

## Overview

This document outlines the strategy for completing Phase 3 (Type System Integration) and beginning Phase 5 (Advanced SMT Features) of the Z3 integration.

---

## Phase 3: Type System Integration - Completion Plan

**Current Status**: 95% Complete (20/21 tests passing)  
**Remaining Work**: Full precondition/postcondition verification, constraint propagation

### 3.1 Precondition/Postcondition Verification

**Goal**: Verify function preconditions and postconditions using SMT

**Current Stubs** (`cure_refinement_types.erl`):
```erlang
verify_precondition(_FunInfo) ->
    {ok, []}.  % Stub: always succeeds

verify_postcondition(_FunInfo) ->
    {ok, []}.  % Stub: always succeeds
```

**Implementation Plan**:

1. **Extract Function Contracts from AST**
   - Parse `@requires` annotations for preconditions
   - Parse `@ensures` annotations for postconditions
   - Extract parameter types with refinements
   - Extract return type with refinements

2. **Verify Preconditions at Call Sites**
   ```erlang
   % Function definition:
   def safe_div(a: Int, b: NonZero) -> Int where b /= 0
   
   % Call site verification:
   def caller(x: Int) -> Int do
       safe_div(10, x)  % Error: x might be 0
   end
   
   % SMT query: Can x be 0?
   % If SAT, report error with counterexample
   ```

3. **Verify Postconditions in Function Bodies**
   ```erlang
   % Function definition:
   def abs_value(x: Int) -> Positive
       ensures result > 0
   do
       if x < 0 then -x else x end
   end
   
   % SMT query: Does the body guarantee result > 0?
   % Check both branches: (-x > 0) when (x < 0)
   %                  and (x > 0) when (x >= 0)
   ```

**Files to Modify**:
- `src/types/cure_refinement_types.erl` - Implement verification logic
- `src/types/cure_typechecker.erl` - Call verification during type checking
- `test/refinement_types_test.erl` - Fix `propagate_constraints_simple_test`

**Estimated Effort**: 2-3 days

### 3.2 Constraint Propagation

**Goal**: Track constraints through control flow and propagate them

**Current Issue**: Test `propagate_constraints_simple_test` fails because `cure_types:lookup_env/2` doesn't exist

**Implementation Plan**:

1. **Add `lookup_env/2` to `cure_types.erl`**
   ```erlang
   -spec lookup_env(atom(), type_env()) -> {ok, type()} | error.
   lookup_env(VarName, Env) ->
       case maps:get(VarName, Env, undefined) of
           undefined -> error;
           Type -> {ok, Type}
       end.
   ```

2. **Implement Constraint Flow Analysis**
   ```erlang
   % Example: if-then-else branches
   if x > 0 then
       % In this branch, we know x > 0
       % Propagate this constraint
       ...
   else
       % In this branch, we know x <= 0
       ...
   end
   ```

3. **Bidirectional Propagation**
   - Forward propagation: from assignments to uses
   - Backward propagation: from required types to actual values

**Files to Modify**:
- `src/types/cure_types.erl` - Add `lookup_env/2`, `add_constraint/3`
- `src/types/cure_refinement_types.erl` - Implement `propagate_constraints/2`
- `src/types/cure_typechecker.erl` - Use constraint propagation in branches

**Estimated Effort**: 3-4 days

### 3.3 Integration with Type Checker

**Goal**: Make SMT verification a natural part of type checking

**Tasks**:
1. Extract refinement types from type annotations
2. Verify subtyping relationships during unification
3. Check preconditions at every function call
4. Verify postconditions in function definitions
5. Propagate constraints through control flow

**File**: `src/types/cure_typechecker.erl`

**Key Integration Points**:
- `check_function_call/4` - Verify preconditions
- `check_function_def/3` - Verify postconditions
- `unify/3` - Use SMT for subtyping
- `check_if_expr/3` - Propagate branch constraints

**Estimated Effort**: 2-3 days

**Total Phase 3 Completion**: 7-10 days

---

## Phase 5: Advanced SMT Features

**Goal**: Leverage SMT for advanced program analysis

**Status**: Not Started (0%)  
**Dependencies**: Phase 3 complete (or partial completion acceptable)

### 5.1 Pattern Exhaustiveness Synthesis

**Goal**: Automatically generate missing pattern match cases using SMT

**Algorithm**:
```
1. Encode covered patterns as SMT constraints
   covered_patterns = (pattern_1 ∨ pattern_2 ∨ ... ∨ pattern_n)

2. Query Z3: Is there a value NOT covered?
   query = ¬covered_patterns
   
3. If SAT:
   - Get model (counterexample) from Z3
   - Convert model to Cure pattern
   - Suggest to user
   - Add to covered_patterns
   - Repeat step 2

4. If UNSAT:
   - All cases covered, pattern match is exhaustive
```

**Example**:
```cure
type Status = Ok | Error(Int) | Pending

match status do
  | Ok -> "done"
  # Missing: Error(_) and Pending
end

# SMT query: status = Error(_) OR status = Pending?
# Z3 returns: SAT, model = {status = Error(404)}
# Suggest: | Error(_) -> ...

# After adding Error(_), query again
# Z3 returns: SAT, model = {status = Pending}
# Suggest: | Pending -> ...

# After adding Pending, query again
# Z3 returns: UNSAT (all cases covered)
```

**Implementation**:

1. **Pattern Encoding** (`src/smt/cure_pattern_encoder.erl`)
   ```erlang
   % Encode pattern as SMT constraint
   encode_pattern(Pattern, Type) ->
       case Pattern of
           {atom, ok} ->
               "(= status ok)";
           {tuple, error, {var, _}} ->
               "(is-error status)";
           {atom, pending} ->
               "(= status pending)"
       end.
   ```

2. **Coverage Analysis** (`src/types/cure_pattern_checker.erl`)
   ```erlang
   % Check if patterns are exhaustive
   check_exhaustiveness(Patterns, Type) ->
       EncodedPatterns = [encode_pattern(P, Type) || P <- Patterns],
       CoveredConstraint = join_with_or(EncodedPatterns),
       
       % Query: NOT covered
       Query = "(not " ++ CoveredConstraint ++ ")",
       
       case cure_smt_solver:check_constraint(Query) of
           {sat, Model} ->
               % Found uncovered case
               MissingPattern = model_to_pattern(Model, Type),
               {incomplete, MissingPattern};
           {unsat, _} ->
               % All cases covered
               {complete}
       end.
   ```

3. **LSP Integration**
   - Add diagnostic for non-exhaustive patterns
   - Code action: "Add missing pattern cases"
   - Automatically insert generated patterns

**Files to Create**:
- `src/smt/cure_pattern_encoder.erl` (150 LOC est.)
- `src/types/cure_pattern_checker.erl` (200 LOC est.)
- `test/pattern_synthesis_test.erl` (100 LOC est.)

**Estimated Effort**: 4-5 days

### 5.2 FSM Verification

**Goal**: Verify finite state machine correctness properties

**Properties to Verify**:
1. **No Deadlocks**: Every state has at least one outgoing transition
2. **Reachability**: All states are reachable from initial state
3. **Liveness**: System can always make progress
4. **Safety**: Bad states are never reached

**Example FSM**:
```cure
fsm TrafficLight do
    states [Green, Yellow, Red]
    initial Green
    
    Green -> Yellow on timer
    Yellow -> Red on timer
    Red -> Green on timer
end

# SMT verifies:
# 1. No deadlocks: ✓ (all states have transitions)
# 2. Reachability: ✓ (all states reachable from Green)
# 3. Liveness: ✓ (always eventually transitions)
# 4. Safety: Define bad states, verify unreachable
```

**Verification Approach**:

1. **Encode FSM as SMT**
   ```smt2
   (declare-datatype State
       ((Green) (Yellow) (Red)))
   
   (declare-fun transition (State) State)
   (assert (= (transition Green) Yellow))
   (assert (= (transition Yellow) Red))
   (assert (= (transition Red) Green))
   ```

2. **Deadlock Detection**
   ```erlang
   % For each state, verify there exists a transition
   check_deadlock(State) ->
       Query = "(exists ((next State)) 
                   (= next (transition " ++ state_to_smt(State) ++ ")))",
       case cure_smt_solver:check_constraint(Query) of
           {unsat, _} -> {deadlock, State};
           {sat, _} -> ok
       end.
   ```

3. **Reachability Analysis**
   ```erlang
   % Use transitive closure or bounded model checking
   check_reachability(Initial, Target, MaxDepth) ->
       % Can we reach Target from Initial in <= MaxDepth steps?
       Query = "(exists ((path (Array Int State)))
                   (and (= (select path 0) " ++ Initial ++ ")
                        (exists ((k Int))
                            (and (<= k " ++ MaxDepth ++ ")
                                 (= (select path k) " ++ Target ++ ")))))",
       cure_smt_solver:check_constraint(Query).
   ```

4. **Temporal Logic (LTL)**
   - Eventually: ◇φ (φ will eventually be true)
   - Always: □φ (φ is always true)
   - Until: φ U ψ (φ until ψ becomes true)

**Implementation**:

**Files to Create**:
- `src/fsm/cure_fsm_verifier.erl` (300 LOC est.)
- `src/smt/cure_fsm_encoder.erl` (200 LOC est.)
- `test/fsm_verification_test.erl` (150 LOC est.)

**Estimated Effort**: 5-6 days

### 5.3 Guard Optimization

**Goal**: Simplify guard conditions using SMT equivalence

**Example**:
```cure
# Before optimization
when x > 0 and x > -1 and x < 100 and x /= 0

# SMT proves: x > 0 implies x > -1 and x /= 0
# Optimized:
when x > 0 and x < 100
```

**Optimization Strategies**:

1. **Redundancy Elimination**
   ```erlang
   % Remove guard G2 if G1 implies G2
   is_redundant(G1, G2) ->
       Implication = "(=> " ++ guard_to_smt(G1) ++ 
                     " " ++ guard_to_smt(G2) ++ ")",
       case cure_smt_solver:prove_constraint(Implication) of
           true -> {redundant, G2};
           false -> not_redundant
       end.
   ```

2. **Guard Reordering**
   ```erlang
   % Reorder guards from most to least selective
   % Use SMT to estimate selectivity (percentage of values passing)
   ```

3. **Constant Folding**
   ```erlang
   % If SMT proves guard is always true, remove it
   % If SMT proves guard is always false, flag as error
   ```

**Files to Create**:
- `src/codegen/cure_guard_optimizer.erl` (250 LOC est.)
- `test/guard_optimization_test.erl` (100 LOC est.)

**Estimated Effort**: 3-4 days

### 5.4 Comprehensive Test Suite

**Goal**: Extensive testing for all Phase 5 features

**Test Files to Create**:
1. `test/z3_integration_comprehensive_test.erl` - End-to-end tests
2. `test/pattern_synthesis_test.erl` - Pattern generation tests
3. `test/fsm_verification_test.erl` - FSM correctness tests
4. `test/guard_optimization_test.erl` - Guard simplification tests

**Example Test Scenarios**:

```erlang
% Pattern synthesis
test_pattern_synthesis_simple() ->
    Code = "
        type Maybe(T) = Just(T) | Nothing
        
        def unwrap(m: Maybe(Int)) -> Int do
            match m do
                | Just(x) -> x
                # Missing: Nothing case
            end
        end
    ",
    {ok, AST} = cure_parser:parse_string(Code),
    {error, {non_exhaustive, MissingPatterns}} = 
        cure_pattern_checker:check_exhaustiveness(AST),
    ?assertEqual([{atom, nothing}], MissingPatterns).

% FSM verification
test_fsm_no_deadlock() ->
    FSM = make_traffic_light_fsm(),
    {ok, States} = cure_fsm_verifier:check_deadlock(FSM),
    ?assertEqual([], States).  % No deadlock states

% Guard optimization
test_guard_redundancy() ->
    Guard = {and, [{op, '>', {var, x}, {lit, 0}},
                   {op, '>', {var, x}, {lit, -1}}]},
    Optimized = cure_guard_optimizer:optimize(Guard),
    Expected = {op, '>', {var, x}, {lit, 0}},
    ?assertEqual(Expected, Optimized).
```

**Estimated Effort**: 2-3 days

**Total Phase 5**: 14-18 days

---

## Implementation Priority

### High Priority (Do First)
1. ✅ Performance profiling infrastructure (DONE)
2. Phase 3 completion:
   - Precondition/postcondition verification
   - Constraint propagation
   - Type checker integration

### Medium Priority (Do Next)
3. Phase 5.1: Pattern exhaustiveness synthesis
4. Phase 5.2: FSM verification (basic features)

### Lower Priority (Later)
5. Phase 5.3: Guard optimization
6. Phase 5.4: Comprehensive testing

---

## Success Metrics

### Phase 3 Complete When:
- ✅ 21/21 refinement type tests passing (currently 20/21)
- ✅ Preconditions verified at call sites
- ✅ Postconditions verified in function bodies
- ✅ Constraints propagate through control flow
- ✅ Integration with type checker seamless

### Phase 5 Complete When:
- ✅ Pattern synthesis suggests missing cases
- ✅ FSM deadlocks detected automatically
- ✅ Guard conditions optimized correctly
- ✅ All Phase 5 tests passing (50+ tests)
- ✅ Documentation complete with examples

---

## Risk Mitigation

### Risk 1: Type Checker Complexity
**Issue**: `cure_typechecker.erl` is large and complex  
**Mitigation**: 
- Make minimal, targeted changes
- Add SMT verification as optional enhancement
- Preserve existing functionality

### Risk 2: SMT Performance
**Issue**: Pattern synthesis may require many Z3 queries  
**Mitigation**:
- Cache synthesis results
- Limit search depth
- Use timeouts aggressively

### Risk 3: FSM State Space Explosion
**Issue**: Large FSMs may have intractable state spaces  
**Mitigation**:
- Bounded model checking (limit depth)
- Abstraction techniques
- User-specified bounds

---

## Next Steps

1. **Immediate** (Today):
   - ✅ Create performance profiling module
   - Start Phase 3 precondition implementation

2. **This Week**:
   - Complete precondition/postcondition verification
   - Implement constraint propagation
   - Fix failing test

3. **Next Week**:
   - Integrate with type checker
   - Begin pattern exhaustiveness synthesis
   - Start FSM verification basics

4. **Following Weeks**:
   - Complete Phase 5 features
   - Comprehensive testing
   - Documentation

---

## Estimated Timeline

| Phase | Tasks | Estimated Time | Status |
|-------|-------|----------------|--------|
| Performance Profiling | Infrastructure | 1 day | ✅ Complete |
| Phase 3.1 | Preconditions/Postconditions | 2-3 days | Pending |
| Phase 3.2 | Constraint Propagation | 3-4 days | Pending |
| Phase 3.3 | Type Checker Integration | 2-3 days | Pending |
| **Phase 3 Total** | | **7-10 days** | **0% Complete** |
| Phase 5.1 | Pattern Synthesis | 4-5 days | Pending |
| Phase 5.2 | FSM Verification | 5-6 days | Pending |
| Phase 5.3 | Guard Optimization | 3-4 days | Pending |
| Phase 5.4 | Testing | 2-3 days | Pending |
| **Phase 5 Total** | | **14-18 days** | **0% Complete** |
| **Grand Total** | | **21-28 days** | |

---

**Status**: Roadmap Complete  
**Last Updated**: 2025-01-25  
**Owner**: Core Compiler Team
