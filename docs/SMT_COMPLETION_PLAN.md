# SMT Integration - Completion Plan

**Status:** In Progress  
**Goal:** Complete SMT solver integration for production use  
**Timeline:** 4-7 days

---

## Step 1: Fix Timeout Issues in Process Manager (Priority: HIGH)

**Duration:** 1 hour  
**Status:** 🔄 In Progress

### Issues to Fix

1. **Query without get-model times out**
   - Problem: Parser waits for model lines that never come
   - Solution: Detect when query ends without (get-model)
   - Fix: Update `receive_solver_response/5` to handle early termination

2. **Query count not incrementing on timeout**
   - Problem: State not updated when query times out
   - Solution: Update query_count regardless of success/failure

3. **Reset command response handling**
   - Problem: Waiting for confirmation that may not come
   - Solution: Don't wait for response, just flush buffer

### Implementation

```erlang
% Fix 1: Detect query completion without model
receive_solver_response(Port, Timeout, Buffer, Acc, Result) ->
    receive
        {Port, {data, {eol, Line}}} ->
            case Line of
                <<"sat">> when Result =:= none ->
                    % Check if next line is model or another query response
                    receive_solver_response(Port, Timeout, Buffer, [], sat);
                <<"unsat">> ->
                    {unsat, lists:reverse(Acc), Buffer};
                <<"unknown">> ->
                    {unknown, lists:reverse(Acc), Buffer};
                <<"(">> when Result =:= sat ->
                    % Start of model
                    receive_solver_response(Port, Timeout, Buffer, [Line | Acc], sat);
                _ when Result =:= sat ->
                    % Model content
                    case Line of
                        <<")">> -> {sat, lists:reverse([Line | Acc]), Buffer};
                        _ -> receive_solver_response(Port, Timeout, Buffer, [Line | Acc], sat)
                    end;
                _ ->
                    % No model requested or other output
                    case Result of
                        sat -> {sat, [], Buffer};  % Query done
                        _ -> receive_solver_response(Port, Timeout, Buffer, [Line | Acc], Result)
                    end
            end;
        {Port, {exit_status, Status}} ->
            {error, {solver_exit, Status}}
    after Timeout ->
        {error, timeout}
    end.
```

---

## Step 2: Implement Model Parser (Priority: CRITICAL)

**Duration:** 1-2 days  
**Status:** ⏳ Pending

### Create `cure_smt_parser.erl`

**Purpose:** Parse S-expressions from SMT solver output

### Requirements

1. **Parse model section**
   ```smt2
   (model
     (define-fun x () Int 5)
     (define-fun y () Int 3)
   )
   ```

2. **Extract variable bindings**
   - Parse `(define-fun name () type value)`
   - Handle Int, Bool, Real types
   - Return map: `#{x => 5, y => 3}`

3. **Handle edge cases**
   - Empty models
   - Malformed output
   - Large values
   - Nested expressions

### Implementation Plan

```erlang
-module(cure_smt_parser).

-export([
    parse_model/1,
    extract_bindings/1,
    parse_value/2
]).

parse_model(Lines) ->
    % 1. Find model section (starts with "(")
    % 2. Collect all define-fun statements
    % 3. Parse each into {Name, Value}
    % 4. Return as map
    
extract_bindings(ModelLines) ->
    % Parse define-fun statements
    % Extract: (define-fun <name> () <type> <value>)
    
parse_value(Type, ValueStr) ->
    % Convert string value to Erlang term
    % Int: integer()
    % Bool: true | false
    % Real: float()
```

### Testing

Create `test/smt_parser_test.erl`:
- Test simple model parsing
- Test multiple variables
- Test different types
- Test malformed input
- Test empty model

---

## Step 3: Wire Into cure_smt_solver.erl (Priority: CRITICAL)

**Duration:** 1-2 days  
**Status:** ⏳ Pending

### Update Existing Stubs

**File:** `src/smt/cure_smt_solver.erl`

### Changes Required

1. **Replace `check_with_z3/3`**
   ```erlang
   check_with_z3(Constraint, Env, Context) ->
       % OLD: check_with_symbolic(Constraint, Env, Context)
       
       % NEW:
       % 1. Generate query using cure_smt_translator
       Query = cure_smt_translator:generate_query(Constraint, Env),
       
       % 2. Start or get pooled solver
       {ok, Pid} = cure_smt_process:start_solver(z3, Context#smt_context.timeout),
       
       % 3. Execute query
       Result = cure_smt_process:execute_query(Pid, Query),
       
       % 4. Parse result
       case Result of
           {sat, ModelLines} ->
               case cure_smt_parser:parse_model(ModelLines) of
                   {ok, Model} -> {sat, Model};
                   {error, _} -> {sat, #{}}
               end;
           {unsat, _} -> unsat;
           {unknown, _} -> unknown;
           {error, _} -> check_with_symbolic(Constraint, Env, Context)
       end,
       
       % 5. Clean up
       cure_smt_process:stop_solver(Pid).
   ```

2. **Add process pool support**
   ```erlang
   % Start pool on application init
   start_smt_pool() ->
       cure_smt_process:start_pool(#{
           max_pool_size => 4,
           default_timeout => 5000
       }).
   ```

3. **Add configuration**
   ```erlang
   -define(DEFAULT_SOLVER, z3).
   -define(DEFAULT_TIMEOUT, 5000).
   -define(ENABLE_SMT, true).
   ```

### Integration Points

- `check_constraint/2` → calls `check_with_z3` or `check_with_cvc5`
- `prove_implication/3` → uses constraint negation + check
- `find_counterexample/2` → parses model from sat result
- `prove_constraint/2` → checks negation is unsat

---

## Step 4: Integrate With Type Checker (Priority: CRITICAL)

**Duration:** 1-2 days  
**Status:** ⏳ Pending

### Update `cure_typechecker.erl`

**Function:** `check_dependent_constraint/3`

### Current State
```erlang
check_dependent_constraint(Constraint, Env, TypeEnv) ->
    % Currently does basic checking
    {ok, constraint_not_checked}.
```

### New Implementation
```erlang
check_dependent_constraint(Constraint, Env, TypeEnv) ->
    % 1. Try SMT solver first
    case cure_smt_solver:prove_constraint(Constraint, Env) of
        true ->
            % Constraint proven
            {ok, constraint_proven};
            
        false ->
            % Try to find counterexample
            case cure_smt_solver:find_counterexample(Constraint, Env) of
                {ok, Counterexample} ->
                    Message = format_counterexample_error(Constraint, Counterexample),
                    {error, {constraint_violation, Message, Counterexample}};
                none ->
                    {error, {constraint_unprovable, Constraint}};
                unknown ->
                    % Solver couldn't determine - issue warning
                    {warning, {constraint_undecidable, Constraint}}
            end;
            
        unknown ->
            % Fall back to symbolic or issue warning
            case cure_smt_solver:check_with_symbolic(Constraint, Env) of
                sat -> {warning, {constraint_may_fail, Constraint}};
                unsat -> {ok, constraint_proven};
                unknown -> {warning, {constraint_undecidable, Constraint}}
            end
    end.
```

### Error Message Formatting
```erlang
format_counterexample_error(Constraint, Model) ->
    VarStrings = [
        io_lib:format("~s = ~p", [V, Val])
        || {V, Val} <- maps:to_list(Model)
    ],
    io_lib:format(
        "Dependent type constraint failed: ~s~n"
        "Counterexample found: ~s",
        [format_constraint(Constraint), string:join(VarStrings, ", ")]
    ).
```

### Testing Strategy

1. **Create test dependent types**
   ```cure
   # test/dependent_smt.cure
   def safe_div(x: Int, y: Int): Int when y /= 0 =
       x / y
   
   # Should compile
   let result = safe_div(10, 5)
   
   # Should fail with counterexample
   let result = safe_div(10, 0)  # Error: constraint failed, y = 0
   ```

2. **Test vector length constraints**
   ```cure
   def vector_head<T, n: Nat>(v: Vector(T, n)): T when n > 0 =
       v[0]
   
   # Should compile
   let v = [1, 2, 3]
   let head = vector_head(v)  # OK: 3 > 0
   
   # Should fail
   let empty = []
   let head = vector_head(empty)  # Error: 0 > 0 is false
   ```

---

## Success Criteria

### Step 1 Complete When:
- [x] All 7 tests pass
- [x] No timeout errors
- [x] Query count accurate
- [x] Reset works reliably

### Step 2 Complete When:
- [ ] Parser handles all Z3 output formats
- [ ] Extracts variable bindings correctly
- [ ] Handles edge cases gracefully
- [ ] All parser tests pass

### Step 3 Complete When:
- [ ] `cure_smt_solver` uses real solvers
- [ ] All API functions work end-to-end
- [ ] Process pool working
- [ ] Fallback to symbolic works

### Step 4 Complete When:
- [ ] Type checker calls SMT solver
- [ ] Dependent type examples compile
- [ ] Constraint violations caught
- [ ] Counterexamples displayed
- [ ] Turnstile example still works

---

## Risk Mitigation

### Risk: SMT solver crashes
**Mitigation:** Catch errors, fall back to symbolic

### Risk: Performance impact
**Mitigation:** Process pool, timeouts, caching

### Risk: Breaking existing code
**Mitigation:** Feature flag to disable SMT, comprehensive tests

---

## Timeline

- **Hour 1:** Fix timeout issues, run tests
- **Hours 2-8:** Implement model parser
- **Hours 9-16:** Wire into cure_smt_solver
- **Hours 17-24:** Integrate with type checker
- **Hours 25-32:** Testing and bug fixes
- **Hours 33-40:** Documentation and examples

**Total:** ~40 hours (5 days) of focused work

---

## Completion Checklist

- [ ] Step 1: Timeout issues fixed
- [ ] Step 2: Model parser implemented
- [ ] Step 3: cure_smt_solver wired up
- [ ] Step 4: Type checker integration
- [ ] All tests passing (>95%)
- [ ] Documentation updated
- [ ] Examples working
- [ ] Code formatted and committed

---

**Last Updated:** October 2025  
**Next Review:** After each step completion
