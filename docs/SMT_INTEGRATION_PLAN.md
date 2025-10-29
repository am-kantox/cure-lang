# SMT Solver Integration Plan for Cure

**Status:** Implementation Plan  
**Priority:** CRITICAL (Main Production Blocker)  
**Estimated Effort:** 2-3 weeks  
**Target Completion:** November 2025

---

## Executive Summary

This document details the complete plan for integrating Z3 and CVC5 SMT solvers into the Cure compiler to enable full dependent type verification. The current implementation has correct architecture but all external solver calls are stubs. This integration is the **critical blocker** preventing production-ready dependent type support.

---

## Part 1: Architecture Overview

### Current State Analysis

**File:** `src/smt/cure_smt_solver.erl` (~900 LOC)

**What Works:**
- ✅ Public API defined (`check_constraint/2`, `prove_implication/3`, etc.)
- ✅ Solver selection mechanism (Z3, CVC5, symbolic fallback)
- ✅ Basic symbolic evaluator for simple constraints
- ✅ Integration hooks in type checker and guard compiler

**What's Missing:**
- ❌ Actual solver process spawning and communication
- ❌ SMT-LIB constraint translation
- ❌ Model extraction from solver output
- ❌ Timeout and resource management
- ❌ Error handling for solver failures

### Target Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                     Cure Type Checker                           │
│  (cure_typechecker.erl - dependent type constraints)           │
└───────────────────┬─────────────────────────────────────────────┘
                    │ check_dependent_constraint/3
                    ▼
┌─────────────────────────────────────────────────────────────────┐
│                  SMT Solver API Layer                           │
│  (cure_smt_solver.erl - public interface)                      │
│  • check_constraint/2    • prove_implication/3                 │
│  • find_counterexample/2 • simplify_constraint/2               │
└───────┬───────────────────────────────┬─────────────────────────┘
        │                               │
        ▼                               ▼
┌──────────────────────┐        ┌──────────────────────┐
│ Constraint Translator│        │ Symbolic Fallback    │
│ (Cure AST → SMT-LIB) │        │ (Basic evaluation)   │
└──────────┬───────────┘        └──────────────────────┘
           │
           ▼
┌─────────────────────────────────────────────────────────────────┐
│              Solver Process Manager                             │
│  • Process pool management                                      │
│  • Timeout enforcement                                          │
│  • Resource limits                                              │
└────┬────────────────────────────────────┬─────────────────────┘
     │                                    │
     ▼                                    ▼
┌─────────────────┐              ┌─────────────────┐
│  Z3 Solver      │              │  CVC5 Solver    │
│  (z3 -smt2)     │              │  (cvc5 --lang   │
│                 │              │   smt2)         │
└────┬────────────┘              └────┬────────────┘
     │                                │
     ▼                                ▼
┌─────────────────────────────────────────────────────────────────┐
│              Model Parser & Result Extractor                    │
│  • Parse s-expressions                                          │
│  • Extract satisfying assignments                               │
│  • Generate counterexamples                                     │
└─────────────────────────────────────────────────────────────────┘
```

---

## Part 2: Implementation Phases

### Phase 1: Environment Setup & Verification (Day 1)

#### 1.1 Check Solver Availability
```bash
# Verify Z3
z3 --version
# Expected: Z3 version 4.8.x or later

# Verify CVC5
cvc5 --version
# Expected: cvc5 version 1.0.x or later
```

#### 1.2 Create Installation Documentation
Document installation for Ubuntu/Debian:
```bash
# Z3
sudo apt-get install z3

# CVC5 (may need to build from source)
wget https://github.com/cvc5/cvc5/releases/download/cvc5-1.0.8/cvc5-Linux
chmod +x cvc5-Linux
sudo mv cvc5-Linux /usr/local/bin/cvc5
```

#### 1.3 Verify SMT-LIB2 Support
Create test files to verify solver SMT-LIB2 compliance:
```smt2
(set-logic QF_LIA)  ; Quantifier-free linear integer arithmetic
(declare-const x Int)
(declare-const y Int)
(assert (> x y))
(assert (> y 0))
(check-sat)
(get-model)
```

**Deliverables:**
- [ ] Solver availability check function
- [ ] Installation guide in docs/
- [ ] SMT-LIB2 compliance tests

---

### Phase 2: Constraint Translation (Days 2-4)

#### 2.1 Design Constraint Translation Module

**New Module:** `cure_smt_translator.erl`

Core responsibilities:
1. Convert Cure AST expressions to SMT-LIB s-expressions
2. Handle type mappings (Int → Int, Nat → Int with constraint, etc.)
3. Variable declaration generation
4. Assertion generation

#### 2.2 Type Mappings

| Cure Type | SMT-LIB Logic | SMT Type | Additional Constraints |
|-----------|---------------|----------|------------------------|
| `Int` | `QF_LIA` | `Int` | none |
| `Nat` | `QF_LIA` | `Int` | `(assert (>= n 0))` |
| `Bool` | `QF_LIA` | `Bool` | none |
| `Float` | `QF_LRA` | `Real` | none |
| `Vector(T, n)` | `QF_LIA` + Arrays | `(Array Int T)` | `(assert (= (length v) n))` |

#### 2.3 Expression Translation Rules

```erlang
% Arithmetic
translate(#binary_op_expr{op = '+', left = L, right = R}) ->
    "(+ " ++ translate(L) ++ " " ++ translate(R) ++ ")".

% Comparisons
translate(#binary_op_expr{op = '<', left = L, right = R}) ->
    "(< " ++ translate(L) ++ " " ++ translate(R) ++ ")".

% Boolean operations
translate(#binary_op_expr{op = 'and', left = L, right = R}) ->
    "(and " ++ translate(L) ++ " " ++ translate(R) ++ ")".

% Variables
translate(#identifier_expr{name = Name}) ->
    atom_to_list(Name).

% Literals
translate(#literal_expr{value = Val}) when is_integer(Val) ->
    integer_to_list(Val).
```

#### 2.4 Complete SMT-LIB Query Generation

```erlang
generate_smt_query(Constraint, Env) ->
    % 1. Determine logic
    Logic = infer_logic(Constraint),
    
    % 2. Collect variables
    Vars = collect_variables(Constraint, Env),
    
    % 3. Generate declarations
    Declarations = [declare_var(V) || V <- Vars],
    
    % 4. Translate constraint
    Assertion = "(assert " ++ translate(Constraint) ++ ")",
    
    % 5. Assemble query
    [
        "(set-logic " ++ Logic ++ ")\n",
        Declarations,
        Assertion ++ "\n",
        "(check-sat)\n",
        "(get-model)\n"
    ].
```

**Deliverables:**
- [ ] `cure_smt_translator.erl` module
- [ ] Type mapping table implementation
- [ ] Expression translation for all operators
- [ ] Complete query generation
- [ ] Unit tests for translation

---

### Phase 3: Solver Process Management (Days 5-7)

#### 3.1 Port-Based Communication

Erlang `port` provides process-like interface to external programs:

```erlang
-record(solver_process, {
    port :: port(),
    solver :: z3 | cvc5,
    pid :: pid(),
    timeout :: integer(),
    start_time :: integer()
}).

% Start solver process
start_solver(z3, Timeout) ->
    Port = open_port({spawn, "z3 -smt2 -in"}, [
        {line, 1024},
        binary,
        exit_status,
        use_stdio
    ]),
    #solver_process{
        port = Port,
        solver = z3,
        pid = self(),
        timeout = Timeout,
        start_time = erlang:monotonic_time(millisecond)
    }.
```

#### 3.2 Query Execution

```erlang
execute_query(SolverProc, Query) ->
    Port = SolverProc#solver_process.port,
    Timeout = SolverProc#solver_process.timeout,
    
    % Send query
    port_command(Port, Query),
    
    % Receive response with timeout
    receive_response(Port, Timeout, []).

receive_response(Port, Timeout, Acc) ->
    receive
        {Port, {data, {eol, Line}}} ->
            case Line of
                <<"sat">> -> {sat, lists:reverse(Acc)};
                <<"unsat">> -> {unsat, []};
                <<"unknown">> -> {unknown, []};
                _ -> receive_response(Port, Timeout, [Line | Acc])
            end;
        {Port, {exit_status, Status}} ->
            {error, {solver_exit, Status}}
    after Timeout ->
        port_close(Port),
        {error, timeout}
    end.
```

#### 3.3 Process Pool Management

To avoid repeated solver startup overhead:

```erlang
-record(solver_pool, {
    z3_processes :: [#solver_process{}],
    cvc5_processes :: [#solver_process{}],
    max_pool_size :: integer(),
    idle_timeout :: integer()
}).

% Get solver from pool or create new
get_solver(Pool, z3) ->
    case Pool#solver_pool.z3_processes of
        [Proc | Rest] ->
            {Proc, Pool#solver_pool{z3_processes = Rest}};
        [] ->
            Proc = start_solver(z3, 5000),
            {Proc, Pool}
    end.

% Return solver to pool
return_solver(Pool, Proc) ->
    reset_solver(Proc),  % Send (reset) command
    case Proc#solver_process.solver of
        z3 -> Pool#solver_pool{
            z3_processes = [Proc | Pool#solver_pool.z3_processes]
        };
        cvc5 -> Pool#solver_pool{
            cvc5_processes = [Proc | Pool#solver_pool.cvc5_processes]
        }
    end.
```

**Deliverables:**
- [ ] Solver process startup/shutdown
- [ ] Port-based communication
- [ ] Timeout enforcement
- [ ] Process pool implementation
- [ ] Resource cleanup on errors

---

### Phase 4: Model Parsing (Days 8-10)

#### 4.1 S-Expression Parser

Need to parse SMT-LIB output like:
```smt2
sat
(model 
  (define-fun x () Int 5)
  (define-fun y () Int 3)
)
```

```erlang
-module(cure_smt_parser).

parse_model(Lines) ->
    % Find model section
    case find_model_section(Lines) of
        {ok, ModelLines} ->
            Bindings = parse_bindings(ModelLines),
            {ok, maps:from_list(Bindings)};
        {error, Reason} ->
            {error, Reason}
    end.

parse_bindings(Lines) ->
    lists:filtermap(fun parse_binding/1, Lines).

% Parse: (define-fun x () Int 5)
parse_binding(Line) ->
    case parse_sexpr(Line) of
        {define_fun, Name, _Type, Value} ->
            {true, {Name, Value}};
        _ ->
            false
    end.
```

#### 4.2 Counterexample Generation

```erlang
generate_counterexample(Model, OriginalVars) ->
    #{
        result => counterexample_found,
        variables => maps:with(OriginalVars, Model),
        message => format_counterexample_message(Model, OriginalVars)
    }.

format_counterexample_message(Model, Vars) ->
    VarStrings = [
        io_lib:format("~s = ~p", [V, maps:get(V, Model)])
        || V <- Vars
    ],
    io_lib:format("Counterexample: ~s", [string:join(VarStrings, ", ")]).
```

**Deliverables:**
- [ ] S-expression parser
- [ ] Model extraction
- [ ] Counterexample generation
- [ ] Error message formatting

---

### Phase 5: Integration with Type Checker (Days 11-13)

#### 5.1 Update `cure_smt_solver.erl`

Replace stub implementations:

```erlang
% OLD (stub):
check_with_z3(Constraint, Env, Context) ->
    check_with_symbolic(Constraint, Env, Context).

% NEW (actual):
check_with_z3(Constraint, Env, Context) ->
    case find_z3() of
        false -> 
            check_with_symbolic(Constraint, Env, Context);
        true ->
            % 1. Translate to SMT-LIB
            Query = cure_smt_translator:generate_query(Constraint, Env),
            
            % 2. Get solver from pool
            {Solver, Pool} = get_solver_from_pool(z3),
            
            % 3. Execute query
            Result = execute_solver_query(Solver, Query, Context),
            
            % 4. Return solver to pool
            return_solver_to_pool(Solver, Pool),
            
            % 5. Parse and return result
            case Result of
                {sat, ModelLines} ->
                    case cure_smt_parser:parse_model(ModelLines) of
                        {ok, Model} -> {sat, Model};
                        {error, _} -> {sat, #{}}
                    end;
                {unsat, _} -> unsat;
                {unknown, _} -> unknown;
                {error, Reason} -> 
                    cure_utils:debug("Z3 error: ~p, falling back~n", [Reason]),
                    check_with_symbolic(Constraint, Env, Context)
            end
    end.
```

#### 5.2 Wire Into Type Checker

Update `cure_typechecker.erl`:

```erlang
check_dependent_constraint(Constraint, Env, TypeEnv) ->
    case cure_smt_solver:prove_constraint(Constraint, Env) of
        true -> 
            {ok, constraint_proven};
        false ->
            % Try to find counterexample
            case cure_smt_solver:find_counterexample(Constraint, Env) of
                {ok, Counterexample} ->
                    {error, {constraint_violation, Counterexample}};
                none ->
                    {error, {constraint_unprovable, Constraint}};
                unknown ->
                    % SMT solver couldn't determine - issue warning
                    {warning, {constraint_undecidable, Constraint}}
            end;
        unknown ->
            {warning, {constraint_undecidable, Constraint}}
    end.
```

**Deliverables:**
- [ ] Replace all stub implementations
- [ ] Integrate with type checker
- [ ] Add warning system for undecidable constraints
- [ ] Error message improvements

---

### Phase 6: Error Handling & Robustness (Day 14)

#### 6.1 Timeout Handling

```erlang
execute_with_timeout(Fun, Timeout) ->
    Parent = self(),
    Ref = make_ref(),
    
    Pid = spawn(fun() ->
        try
            Result = Fun(),
            Parent ! {Ref, {ok, Result}}
        catch
            Class:Reason:Stack ->
                Parent ! {Ref, {error, {Class, Reason, Stack}}}
        end
    end),
    
    receive
        {Ref, Result} -> Result
    after Timeout ->
        exit(Pid, kill),
        {error, timeout}
    end.
```

#### 6.2 Solver Crash Recovery

```erlang
handle_solver_crash(SolverProc, Error) ->
    % Log error
    cure_utils:debug("Solver ~p crashed: ~p~n", 
        [SolverProc#solver_process.solver, Error]),
    
    % Clean up port
    catch port_close(SolverProc#solver_process.port),
    
    % Remove from pool
    remove_from_pool(SolverProc),
    
    % Optionally restart
    case should_restart(Error) of
        true -> start_solver(SolverProc#solver_process.solver, 5000);
        false -> ok
    end.
```

#### 6.3 Resource Limits

```erlang
-define(MAX_MEMORY_MB, 512).
-define(MAX_SOLVER_PROCESSES, 4).
-define(SOLVER_IDLE_TIMEOUT, 60000).  % 1 minute

enforce_resource_limits() ->
    % Check memory usage
    case erlang:memory(total) div (1024 * 1024) of
        Mem when Mem > ?MAX_MEMORY_MB * ?MAX_SOLVER_PROCESSES ->
            cleanup_idle_solvers();
        _ -> ok
    end,
    
    % Check process count
    PoolSize = get_pool_size(),
    case PoolSize of
        N when N > ?MAX_SOLVER_PROCESSES ->
            kill_oldest_solver();
        _ -> ok
    end.
```

**Deliverables:**
- [ ] Timeout handling
- [ ] Crash recovery
- [ ] Resource limits
- [ ] Graceful degradation

---

### Phase 7: Testing (Days 15-16)

#### 7.1 Unit Tests

Create `test/smt_solver_test.erl`:

```erlang
-module(smt_solver_test).
-export([run/0]).

run() ->
    io:format("=== SMT Solver Integration Tests ===~n"),
    
    Tests = [
        fun test_basic_arithmetic/0,
        fun test_constraint_satisfaction/0,
        fun test_implication_proving/0,
        fun test_counterexample_generation/0,
        fun test_dependent_types/0,
        fun test_timeout_handling/0,
        fun test_solver_fallback/0
    ],
    
    run_tests(Tests).

test_basic_arithmetic() ->
    % x + y > 10, x = 5, y = 6
    Constraint = make_constraint("+", var(x), var(y), ">", lit(10)),
    Env = #{x => 5, y => 6},
    
    Result = cure_smt_solver:check_constraint(Constraint, Env),
    assert_equals(sat, Result).
```

#### 7.2 Integration Tests

Test with actual dependent type examples:

```cure
# test_length_indexed_vector.cure
def safe_head<T, n: Nat>(v: Vector(T, n)): Option(T) when n > 0 =
  Some(v[0])

# This should compile (constraint provable)
let v = [1, 2, 3]  # Vector(Int, 3)
let head = safe_head(v)  # Constraint: 3 > 0 → proved by SMT solver

# This should fail (constraint unprovable)
let empty = []  # Vector(Int, 0)
let head = safe_head(empty)  # Constraint: 0 > 0 → false, error!
```

#### 7.3 Performance Tests

```erlang
test_performance() ->
    Constraints = generate_test_constraints(1000),
    
    Start = erlang:monotonic_time(millisecond),
    Results = [cure_smt_solver:check_constraint(C, #{}) || C <- Constraints],
    End = erlang:monotonic_time(millisecond),
    
    AvgTime = (End - Start) / length(Constraints),
    io:format("Average constraint check time: ~p ms~n", [AvgTime]),
    
    % Should be < 10ms per constraint
    assert(AvgTime < 10.0).
```

**Deliverables:**
- [ ] Unit test suite
- [ ] Integration tests with type checker
- [ ] Performance benchmarks
- [ ] Regression tests

---

### Phase 8: Documentation & Polish (Day 17)

#### 8.1 User Documentation

Create `docs/DEPENDENT_TYPES.md`:
- Explain dependent type constraints
- Show SMT solver usage examples
- Document solver installation
- Troubleshooting guide

#### 8.2 API Documentation

Update module docs with `-doc` attributes:

```erlang
-doc """
Checks if a constraint is satisfiable using an SMT solver.

This function translates the Cure constraint to SMT-LIB format and
queries Z3 or CVC5 to determine satisfiability.

## Arguments
- `Constraint` - Cure AST expression representing the constraint
- `Env` - Environment mapping variables to types/values

## Returns
- `sat` - Constraint is satisfiable
- `{sat, Model}` - Satisfiable with variable assignments
- `unsat` - Constraint is unsatisfiable
- `unknown` - Solver couldn't determine (timeout/complexity)

## Examples
```erlang
% x > 0
Constraint = #binary_op_expr{op = '>', left = var(x), right = lit(0)},
cure_smt_solver:check_constraint(Constraint, #{x => {type, int}}).
% => sat
```
""".
```

#### 8.3 Configuration

Add solver configuration to cure CLI:

```bash
cure --smt-solver z3 example.cure
cure --smt-timeout 10000 example.cure
cure --no-smt example.cure  # Disable SMT, use symbolic only
```

**Deliverables:**
- [ ] User documentation
- [ ] API documentation
- [ ] Configuration options
- [ ] Example programs

---

## Part 3: Implementation Timeline

### Week 1: Core Implementation
- **Day 1**: Environment setup, solver verification
- **Day 2-4**: Constraint translation module
- **Day 5-7**: Solver process management

### Week 2: Integration & Testing
- **Day 8-10**: Model parsing and extraction
- **Day 11-13**: Type checker integration
- **Day 14**: Error handling and robustness

### Week 3: Testing & Polish
- **Day 15-16**: Comprehensive testing
- **Day 17**: Documentation and final polish

### Buffer: Days 18-21
- Handle unexpected issues
- Additional testing
- Performance optimization

---

## Part 4: Success Criteria

### Must Have (P0)
- [ ] Z3 integration working for basic arithmetic constraints
- [ ] Constraint translation for all core operators
- [ ] Model extraction and counterexample generation
- [ ] Integration with type checker for dependent types
- [ ] Basic error handling and timeouts

### Should Have (P1)
- [ ] CVC5 integration as alternative solver
- [ ] Process pool for performance
- [ ] Comprehensive test suite
- [ ] User documentation

### Nice to Have (P2)
- [ ] Automatic solver selection based on constraint type
- [ ] Constraint simplification before sending to solver
- [ ] Caching of solver results
- [ ] Parallel constraint checking

---

## Part 5: Risk Mitigation

### Risk: Solver Not Available
**Mitigation:** Keep symbolic fallback functional. Document installation clearly.

### Risk: Performance Issues
**Mitigation:** Implement timeouts, process pooling, and result caching.

### Risk: SMT-LIB Translation Complexity
**Mitigation:** Start with simple constraints, incrementally add complex types.

### Risk: Integration Breaks Existing Code
**Mitigation:** Comprehensive test suite, feature flags to disable SMT.

---

## Part 6: Validation Plan

After implementation, validate with:

1. **Existing Examples**: Ensure `examples/turnstile.cure` still works
2. **Dependent Type Examples**: Create and verify vector, bounded int examples
3. **Negative Tests**: Ensure invalid constraints are caught
4. **Performance**: Measure compilation time impact
5. **Regression**: Run full test suite

---

## Appendix A: SMT-LIB Reference

### Basic Syntax
```smt2
(set-logic QF_LIA)              ; Set logic
(declare-const x Int)           ; Declare variable
(assert (> x 0))                ; Add constraint
(check-sat)                      ; Check satisfiability
(get-model)                      ; Get satisfying assignment
```

### Common Operators
- Arithmetic: `+`, `-`, `*`, `div`, `mod`
- Comparison: `=`, `<`, `>`, `<=`, `>=`
- Boolean: `and`, `or`, `not`, `=>`, `iff`
- Quantifiers: `forall`, `exists`

---

## Appendix B: Z3 vs CVC5 Comparison

| Feature | Z3 | CVC5 |
|---------|----|----|
| **Maturity** | Very mature | Newer |
| **Performance** | Excellent | Excellent |
| **Theories** | Comprehensive | Comprehensive |
| **Installation** | Easy (apt) | May need build |
| **License** | MIT | BSD-3 |
| **Recommendation** | **Primary** | Fallback |

---

**Document Version:** 1.0  
**Created:** October 2025  
**Last Updated:** October 2025
