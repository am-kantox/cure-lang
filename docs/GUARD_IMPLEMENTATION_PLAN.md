# Guard Implementation Plan

## Executive Summary

This document outlines the step-by-step implementation plan to achieve full Erlang-style guard support in Cure, including multi-clause functions with guards.

---

## Phase 1: Complete Single-Clause Function Guards ✅ IN PROGRESS

### Goal
Ensure single-clause functions with guards work correctly end-to-end.

### Tasks

#### Task 1.1: Verify BEAM Code Generation
**Status:** Need to check  
**Files:** `src/codegen/cure_beam_compiler.erl`

**Action Items:**
1. Find how `guard_check` instruction is converted to Erlang abstract form
2. Verify it generates proper Erlang `when` guards in compiled functions
3. Test generated BEAM code loads and executes correctly

**Implementation:**
```erlang
% In cure_beam_compiler.erl, ensure guard_check instruction generates:
{function, Line, FunctionName, Arity, [
  {clause, Line, Params, Guards, Body}
]}
% Where Guards = [[GuardExpr1, GuardExpr2, ...]]
```

#### Task 1.2: Test Guard Evaluation
**Status:** Need comprehensive tests  
**Files:** `test/function_guards_test.erl` (new)

**Test Cases:**
1. Simple comparison guards (`when x > 0`)
2. Boolean logic guards (`when x > 0 and y < 10`)
3. Arithmetic in guards (`when x + y > z`)
4. Type guards (`when is_integer(x)`)
5. Guard failure handling
6. Multiple parameters with guards
7. Complex guard expressions

**Example Test:**
```erlang
test_simple_guard() ->
    Code = "
        module TestGuard do
          def is_positive(x: Int): Bool when x > 0 = true
          def is_positive(x: Int): Bool = false
        end
    ",
    {ok, Module} = compile_and_load(Code),
    ?assertEqual(true, Module:is_positive(5)),
    ?assertEqual(false, Module:is_positive(-3)).
```

#### Task 1.3: Guard Failure Error Messages
**Status:** Need to implement  
**Files:** `src/codegen/cure_codegen.erl`, `src/runtime/cure_runtime.erl`

**Requirements:**
- When a guard fails, generate clear error message
- Include function name, parameters, and failed guard
- Stack trace should be helpful

**Error Format:**
```
** Exception: function_clause
   in function  Module:function_name/2
      called with arguments: (5, 0)
   guard failed: divisor != 0
```

---

## Phase 2: Multi-Clause Functions with Guards 📝 PLANNED

### Goal
Support Erlang-style multi-clause functions where each clause has optional guards.

### Syntax Examples
```cure
% Multiple clauses for same function
def abs(x: Int): Int when x >= 0 = x
def abs(x: Int): Int when x < 0 = -x

def factorial(n: Int): Int when n == 0 = 1
def factorial(n: Int): Int when n > 0 = n * factorial(n - 1)
```

### Tasks

#### Task 2.1: Parser Enhancement
**Status:** Design phase  
**Files:** `src/parser/cure_parser.erl`

**Current Behavior:**
```erlang
% Input: 
%   def abs(x: Int): Int when x >= 0 = x
%   def abs(x: Int): Int when x < 0 = -x

% Currently produces TWO separate function_def records:
#function_def{name = abs, clauses = [Clause1]}
#function_def{name = abs, clauses = [Clause2]}
```

**Desired Behavior:**
```erlang
% Should produce ONE function_def with TWO clauses:
#function_def{
  name = abs,
  clauses = [
    #function_clause{constraint = (x >= 0), body = x},
    #function_clause{constraint = (x < 0), body = -x}
  ]
}
```

**Implementation Strategy:**

**Option A: Post-Parse Grouping** (RECOMMENDED)
- Parse all module items as currently done
- Add `group_function_clauses/1` post-processing step
- Group functions by `{Name, Arity}` key
- Merge into single `#function_def` with multiple clauses

**Advantages:**
- Minimal parser changes
- Easy to implement
- Preserves backward compatibility

**Implementation:**
```erlang
% In parse_module_items/2, after collecting all items:
parse_module_items(State, Acc) ->
    {Items, NewState} = parse_module_items_raw(State, []),
    GroupedItems = group_function_clauses(Items),
    {GroupedItems, NewState}.

group_function_clauses(Items) ->
    % 1. Separate functions from other items
    {Functions, OtherItems} = partition_functions(Items),
    
    % 2. Group functions by {Name, Arity}
    GroupedFunctions = group_by_name_arity(Functions),
    
    % 3. Merge multi-clause functions
    MergedFunctions = merge_function_clauses(GroupedFunctions),
    
    % 4. Combine back with other items
    MergedFunctions ++ OtherItems.
```

**Option B: Parser State Tracking** (Alternative)
- Maintain map of `{Name, Arity} -> ClausesList` in parser state
- When parsing function, check if name/arity already exists
- If yes, append clause; if no, create new entry
- Finalize all functions at end of module

**Disadvantages:**
- More complex parser state
- Harder to maintain clause order across file

#### Task 2.2: Clause Order Verification
**Status:** Design phase

**Requirements:**
- Maintain declaration order (first match wins semantics)
- Verify all clauses have same arity
- Verify return types are compatible
- Check for unreachable clauses (optional warning)

**Example Checks:**
```cure
% ERROR: Arity mismatch
def foo(x: Int): Int = x
def foo(x: Int, y: Int): Int = x + y  % Different arity!

% WARNING: Unreachable clause
def bar(x: Int): Int when x > 0 = x
def bar(x: Int): Int when x > 5 = x * 2  % Never matches!
def bar(x: Int): Int = -x
```

#### Task 2.3: Codegen for Multi-Clause Functions
**Status:** Design phase  
**Files:** `src/codegen/cure_codegen.erl`, `src/codegen/cure_beam_compiler.erl`

**Current State:**
- `compile_multiclause_function/4` exists (lines 1032-1078)
- Handles multiple clauses
- But only called when `length(Clauses) > 1`

**Enhancement Needed:**
Ensure each clause's guard is properly compiled and attached to the Erlang clause.

**BEAM Output:**
```erlang
% Erlang abstract form should be:
{function, Line, abs, 1, [
  {clause, Line1, 
    [{var, Line1, 'X'}],
    [[{op, Line1, '>=', {var, Line1, 'X'}, {integer, Line1, 0}}]],  % Guard!
    [{var, Line1, 'X'}]
  },
  {clause, Line2,
    [{var, Line2, 'X'}],
    [[{op, Line2, '<', {var, Line2, 'X'}, {integer, Line2, 0}}]],  % Guard!
    [{op, Line2, '-', {var, Line2, 'X'}}]
  }
]}
```

**Implementation:**
```erlang
% In cure_beam_compiler.erl
compile_function_clause_to_abstract_form(ClauseInfo, Line) ->
    #{
        params => Params,
        param_names => ParamNames,
        guard_instructions => GuardInstrs,
        body_instructions => BodyInstrs
    } = ClauseInfo,
    
    % Convert guard instructions to Erlang guard expressions
    GuardExprs = convert_guard_instructions_to_abstract(GuardInstrs),
    
    % Convert body instructions to Erlang expressions
    BodyExprs = convert_body_instructions_to_abstract(BodyInstrs),
    
    % Build clause
    {clause, Line,
        build_param_patterns(ParamNames, Line),
        GuardExprs,  % [[Guard1, Guard2, ...]]
        BodyExprs
    }.
```

---

## Phase 3: Type System Integration 🔮 FUTURE

### Goal
Use guard constraints to refine types within function bodies.

### Tasks

#### Task 3.1: Extract Guard Constraints
Extract type constraints from guards for use in type checking.

**Example:**
```cure
def process(x: Int) when x > 0 = 
    % Inside body, treat x as Positive type
    % Enable: let y: Positive = x  % No error!
    ...
```

#### Task 3.2: Flow-Sensitive Typing
Narrow types based on guard success.

**Example:**
```cure
type Positive = Int when x > 0

def compute(x: Int): Positive when x > 0 =
    % Type checker knows: x : Positive here
    % Can call functions requiring Positive without cast
    requires_positive(x)  % OK!
```

#### Task 3.3: Return Type Unification
Ensure all clauses return compatible types.

**Example:**
```cure
% OK: Both return Int
def abs(x: Int): Int when x >= 0 = x
def abs(x: Int): Int when x < 0 = -x

% ERROR: Incompatible return types
def bad(x: Int): Int when x > 0 = x
def bad(x: Int): String when x <= 0 = "negative"  % Type error!
```

---

## Phase 4: Advanced Features & Polish 🎨 FUTURE

### Task 4.1: Guard Sequences
Support `,` (and) and `;` (or) in guards.

**Erlang syntax:**
```erlang
when X > 0, Y > 0  % Both must be true
when X > 0; Y > 0  % Either can be true
```

**Cure syntax:**
```cure
def foo(x: Int, y: Int): Int when x > 0, y > 0 = x + y
def bar(x: Int, y: Int): Int when x > 0; y > 0 = max(x, y)
```

### Task 4.2: Better Optimization
- Detect overlapping guards at compile time
- Warn about unreachable clauses
- Optimize guard evaluation order
- Constant propagation through guards

### Task 4.3: Enhanced Error Messages
- Show which clause was attempted
- Show guard evaluation trace
- Suggest fixes for common guard failures

**Example:**
```
Error: No matching function clause for safe_div/2

Attempted clauses:
  1. safe_div(10, 0): FAILED guard (divisor != 0)
  
Suggestion: Divisor must be non-zero. Consider handling zero case explicitly.
```

---

## Implementation Schedule

### Week 1: Phase 1 (Single-Clause Guards)
- [ ] Day 1-2: Verify BEAM code generation
- [ ] Day 3-4: Comprehensive testing
- [ ] Day 5: Error message improvements

### Week 2: Phase 2 (Multi-Clause Functions)
- [ ] Day 1-3: Parser enhancement (grouping)
- [ ] Day 4: Clause verification
- [ ] Day 5: Codegen integration

### Week 3: Testing & Documentation
- [ ] Day 1-2: Integration tests
- [ ] Day 3: Performance testing
- [ ] Day 4-5: Documentation and examples

---

## Testing Strategy

### Unit Tests
- `test/guard_compilation_test.erl` - Guard compiler
- `test/function_guards_test.erl` - Function-level guards (NEW)
- `test/multiclause_guards_test.erl` - Multi-clause functions (NEW)

### Integration Tests
- Compile and run `examples/05_function_guards.cure`
- Test all guard features end-to-end
- Verify BEAM bytecode correctness

### Regression Tests
- Ensure existing guard functionality (match, FSM) still works
- No performance regressions
- Backward compatibility maintained

---

## Success Criteria

### Phase 1 Complete When:
- [x] Single-clause functions with guards compile
- [ ] Guards evaluate correctly at runtime
- [ ] Guard failures produce clear errors
- [ ] All test cases pass

### Phase 2 Complete When:
- [ ] Multi-clause functions parse correctly
- [ ] Clauses are grouped by name/arity
- [ ] Generated BEAM code is correct
- [ ] `examples/05_function_guards.cure` runs successfully

### Full Implementation Complete When:
- [ ] All phases complete
- [ ] Documentation updated
- [ ] Examples added
- [ ] Performance acceptable
- [ ] No regressions in existing features

---

## Risk Assessment

### Low Risk
- Phase 1 (most infrastructure exists)
- Guard compiler (already complete)
- Testing (good foundation exists)

### Medium Risk
- Parser modification (grouping logic)
- BEAM code generation (complexity)
- Error messages (UX consideration)

### High Risk
- Type system integration (complex)
- Performance impact (needs measurement)
- Edge cases in clause ordering

---

## Dependencies

### Required
- Existing guard compiler infrastructure
- BEAM compiler module
- Type system (for Phase 3)

### Optional
- Z3 integration (for guard verification)
- LSP support (for editor features)
- Profiler (for optimization)

---

## Next Steps

**Immediate (Today):**
1. Verify `cure_beam_compiler.erl` handles guard instructions
2. Create basic function guard test
3. Test compilation end-to-end

**Short-term (This Week):**
1. Complete Phase 1 testing
2. Start parser grouping design
3. Document findings

**Medium-term (Next 2 Weeks):**
1. Implement Phase 2
2. Comprehensive testing
3. Update documentation

---

## References

- **Status Report:** `docs/GUARD_IMPLEMENTATION_STATUS.md`
- **Example Code:** `examples/05_function_guards.cure`
- **Existing Tests:** `test/guard_compilation_test.erl`
- **Parser Code:** `src/parser/cure_parser.erl`
- **Codegen Code:** `src/codegen/cure_codegen.erl`
- **BEAM Compiler:** `src/codegen/cure_beam_compiler.erl`
