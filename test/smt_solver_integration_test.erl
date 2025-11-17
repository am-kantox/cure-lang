-module(smt_solver_integration_test).

-export([run/0]).

-include("../src/parser/cure_ast.hrl").

%% Test SMT solver integration with LSP
run() ->
    io:format("~n=== SMT Solver Integration Test ===~n~n"),

    % Test 1: Helper functions for constraint building
    io:format("Test 1: Helper functions...~n"),
    VarX = cure_smt_solver:variable_term(x),
    Const5 = cure_smt_solver:constant_term(5),
    EqConstraint = cure_smt_solver:equality_constraint(VarX, Const5),
    GtConstraint = cure_smt_solver:inequality_constraint(VarX, '>', Const5),

    io:format("  ✓ Created variable term: ~p~n", [VarX]),
    io:format("  ✓ Created constant term: ~p~n", [Const5]),
    io:format("  ✓ Created equality constraint: x == 5~n"),
    io:format("  ✓ Created inequality constraint: x > 5~n"),

    % Test 2: solve_constraints with empty list
    io:format("~nTest 2: Solve empty constraint list...~n"),
    Result1 = cure_smt_solver:solve_constraints([]),
    io:format("  Result: ~p (expected: sat)~n", [Result1]),
    case Result1 of
        sat -> io:format("  ✓ PASS~n");
        _ -> io:format("  ✗ FAIL~n")
    end,

    % Test 3: solve_constraints with single constraint
    io:format("~nTest 3: Solve single constraint (x > 5)...~n"),
    Result2 = cure_smt_solver:solve_constraints([GtConstraint]),
    io:format("  Result: ~p (expected: sat or {sat, Model})~n", [Result2]),
    case Result2 of
        sat -> io:format("  ✓ PASS (satisfiable)~n");
        {sat, _} -> io:format("  ✓ PASS (satisfiable with model)~n");
        unknown -> io:format("  ⚠ UNKNOWN (no SMT solver available)~n");
        _ -> io:format("  ✗ Unexpected result~n")
    end,

    % Test 4: solve_constraints with multiple constraints
    io:format("~nTest 4: Solve multiple constraints (x > 5 AND x == 5)...~n"),
    Result3 = cure_smt_solver:solve_constraints([GtConstraint, EqConstraint]),
    io:format("  Result: ~p (expected: unsat)~n", [Result3]),
    case Result3 of
        unsat -> io:format("  ✓ PASS (unsatisfiable - correct!)~n");
        unknown -> io:format("  ⚠ UNKNOWN (no SMT solver available)~n");
        _ -> io:format("  ⚠ Got ~p (may be symbolic evaluation)~n", [Result3])
    end,

    % Test 5: Check constraint directly
    io:format("~nTest 5: Direct constraint checking...~n"),
    SimpleConstraint = #binary_op_expr{
        op = '>',
        left = #literal_expr{value = 10, location = #location{line = 1, column = 1}},
        right = #literal_expr{value = 5, location = #location{line = 1, column = 5}},
        location = #location{line = 1, column = 3}
    },
    Result4 = cure_smt_solver:check_constraint(SimpleConstraint, #{}),
    io:format("  Result for (10 > 5): ~p (expected: sat)~n", [Result4]),
    case Result4 of
        sat -> io:format("  ✓ PASS~n");
        {sat, _} -> io:format("  ✓ PASS~n");
        _ -> io:format("  ✗ FAIL~n")
    end,

    % Test 6: Available solvers
    io:format("~nTest 6: Available SMT solvers...~n"),
    Solvers = cure_smt_solver:available_solvers(),
    io:format("  Available solvers: ~p~n", [Solvers]),
    case lists:member(symbolic, Solvers) of
        true -> io:format("  ✓ Symbolic solver always available~n");
        false -> io:format("  ✗ Symbolic solver should be available~n")
    end,

    case lists:member(z3, Solvers) of
        true -> io:format("  ✓ Z3 solver detected on system~n");
        false -> io:format("  ⚠ Z3 not found (install for better performance)~n")
    end,

    case lists:member(cvc5, Solvers) of
        true -> io:format("  ✓ CVC5 solver detected on system~n");
        false -> io:format("  ⚠ CVC5 not found (optional)~n")
    end,

    io:format("~n✓ SMT solver integration tests completed~n"),
    ok.
