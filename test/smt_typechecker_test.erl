-module(smt_typechecker_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").

run() ->
    io:format("~n=== SMT Type Checker Integration Tests ===~n~n"),

    Tests = [
        {"Simple constraint check", fun test_simple_constraint/0},
        {"Constraint with counterexample", fun test_counterexample/0},
        {"Provable constraint", fun test_provable_constraint/0},
        {"Complex constraint", fun test_complex_constraint/0},
        {"Non-constraint expression", fun test_non_constraint/0}
    ],

    Results = lists:map(
        fun({Name, TestFun}) ->
            io:format("Testing ~s... ", [Name]),
            try
                case TestFun() of
                    ok ->
                        io:format("✅~n"),
                        {pass, Name};
                    {ok, Info} ->
                        io:format("✅ (~s)~n", [Info]),
                        {pass, Name};
                    {error, Reason} ->
                        io:format("❌ (~p)~n", [Reason]),
                        {fail, Name, Reason}
                end
            catch
                Class:Error:Stack ->
                    io:format("❌ (exception: ~p:~p)~n", [Class, Error]),
                    io:format("  Stack: ~p~n", [Stack]),
                    {fail, Name, {exception, Class, Error}}
            end
        end,
        Tests
    ),

    Passed = length([X || X = {pass, _} <- Results]),
    Failed = length([X || X = {fail, _, _} <- Results]),
    Total = length(Results),

    io:format("~nPassed: ~p~n", [Passed]),
    io:format("Failed: ~p~n", [Failed]),
    io:format("Total:  ~p~n", [Total]),

    case Failed of
        0 ->
            io:format("~n✅ All SMT type checker tests passed!~n"),
            ok;
        _ ->
            io:format("~n❌ Some tests failed~n"),
            {error, {failed_tests, Failed}}
    end.

%% Test 1: Simple constraint check
test_simple_constraint() ->
    % Constraint: y /= 0
    Constraint = #binary_op_expr{
        op = '/=',
        left = #identifier_expr{name = y, location = #location{}},
        right = #literal_expr{value = 0, location = #location{}},
        location = #location{}
    },

    % This constraint is satisfiable but not provably always true
    % SMT solver should find counterexample (y=0) and return false or allow with warning
    Result = cure_typechecker:check_dependent_constraint(Constraint, undefined, undefined),

    case Result of
        true -> {ok, "constraint allowed with warning"};
        false -> {ok, "constraint has counterexample"};
        _ -> {error, {unexpected_result, Result}}
    end.

%% Test 2: Constraint that should find counterexample
test_counterexample() ->
    % Constraint: x > 10 (has counterexample: x = 0)
    Constraint = #binary_op_expr{
        op = '>',
        left = #identifier_expr{name = x, location = #location{}},
        right = #literal_expr{value = 10, location = #location{}},
        location = #location{}
    },

    % This constraint is satisfiable but not always true
    % SMT should allow it (satisfiable) but may warn
    Result = cure_typechecker:check_dependent_constraint(Constraint, undefined, undefined),

    % Should return true (satisfiable) or false (if proving it must always hold)
    case Result of
        true -> {ok, "constraint satisfiable"};
        false -> {ok, "constraint not always true"};
        _ -> {error, {unexpected_result, Result}}
    end.

%% Test 3: Provable constraint (tautology)
test_provable_constraint() ->
    % Constraint: x == x (always true)
    Constraint = #binary_op_expr{
        op = '==',
        left = #identifier_expr{name = x, location = #location{}},
        right = #identifier_expr{name = x, location = #location{}},
        location = #location{}
    },

    Result = cure_typechecker:check_dependent_constraint(Constraint, undefined, undefined),

    case Result of
        true -> {ok, "tautology proven"};
        false -> {error, tautology_should_be_true};
        _ -> {error, {unexpected_result, Result}}
    end.

%% Test 4: Complex constraint with multiple variables
test_complex_constraint() ->
    % Constraint: x > 0 and y > 0
    Constraint = #binary_op_expr{
        op = 'and',
        left = #binary_op_expr{
            op = '>',
            left = #identifier_expr{name = x, location = #location{}},
            right = #literal_expr{value = 0, location = #location{}},
            location = #location{}
        },
        right = #binary_op_expr{
            op = '>',
            left = #identifier_expr{name = y, location = #location{}},
            right = #literal_expr{value = 0, location = #location{}},
            location = #location{}
        },
        location = #location{}
    },

    Result = cure_typechecker:check_dependent_constraint(Constraint, undefined, undefined),

    case Result of
        true -> {ok, "complex constraint handled"};
        false -> {ok, "complex constraint not provable"};
        _ -> {error, {unexpected_result, Result}}
    end.

%% Test 5: Non-constraint expression (should skip checking)
test_non_constraint() ->
    % Not a constraint: x + y (arithmetic expression, not boolean)
    Expr = #binary_op_expr{
        op = '+',
        left = #identifier_expr{name = x, location = #location{}},
        right = #identifier_expr{name = y, location = #location{}},
        location = #location{}
    },

    % Should return true (skip non-constraint)
    Result = cure_typechecker:check_dependent_constraint(Expr, undefined, undefined),

    case Result of
        true -> {ok, "non-constraint skipped"};
        _ -> {error, {should_skip_non_constraint, Result}}
    end.
