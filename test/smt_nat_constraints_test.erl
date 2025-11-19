%% Test for automatic Nat constraint generation in SMT queries
-module(smt_nat_constraints_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").

run() ->
    io:format("~n=== SMT Nat Constraints Test ===~n~n"),

    Tests = [
        fun test_nat_variable_generates_constraint/0,
        fun test_int_variable_no_constraint/0,
        fun test_mixed_nat_int_variables/0,
        fun test_nat_in_formula/0
    ],

    Results = lists:map(fun run_test/1, Tests),

    Passed = length([R || R <- Results, R =:= ok]),
    Failed = length(Results) - Passed,

    io:format("~n=== Results ===~n"),
    io:format("Passed: ~p~n", [Passed]),
    io:format("Failed: ~p~n", [Failed]),

    case Failed of
        0 -> io:format("~n✅ All Nat constraint tests passed!~n~n");
        _ -> io:format("~n❌ Some Nat constraint tests failed!~n~n")
    end,

    ok.

run_test(TestFun) ->
    try
        TestFun(),
        ok
    catch
        Class:Reason:Stack ->
            io:format("  ❌ FAILED: ~p:~p~n", [Class, Reason]),
            io:format("     Stack: ~p~n", [Stack]),
            error
    end.

%% ============================================================================
%% Test: Nat Variable Generates Constraint
%% ============================================================================

test_nat_variable_generates_constraint() ->
    io:format("Testing Nat variable generates (>= n 0) constraint... "),

    % Simple constraint: n > 5 (where n: Nat)
    Constraint = #binary_op_expr{
        op = '>',
        left = #identifier_expr{name = n, location = #location{line = 1, column = 1}},
        right = #literal_expr{value = 5, location = #location{line = 1, column = 1}},
        location = #location{line = 1, column = 1}
    },

    Env = #{n => {type, nat}},
    Query = cure_smt_translator:generate_query(Constraint, Env, #{}),
    QueryStr = iolist_to_binary(Query),

    % Check that query contains (assert (>= n 0))
    HasNatConstraint = binary:match(QueryStr, <<"(assert (>= n 0))">>) =/= nomatch,
    HasMainConstraint = binary:match(QueryStr, <<"(assert (> n 5))">>) =/= nomatch,

    case HasNatConstraint and HasMainConstraint of
        true ->
            io:format("✅ Nat constraint generated~n"),
            ok;
        false ->
            io:format("❌ Expected Nat constraint, got: ~s~n", [QueryStr]),
            error(missing_nat_constraint)
    end.

%% ============================================================================
%% Test: Int Variable No Constraint
%% ============================================================================

test_int_variable_no_constraint() ->
    io:format("Testing Int variable does NOT generate constraint... "),

    % Simple constraint: x > 5 (where x: Int)
    Constraint = #binary_op_expr{
        op = '>',
        left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
        right = #literal_expr{value = 5, location = #location{line = 1, column = 1}},
        location = #location{line = 1, column = 1}
    },

    Env = #{x => {type, int}},
    Query = cure_smt_translator:generate_query(Constraint, Env, #{}),
    QueryStr = iolist_to_binary(Query),

    % Check that query does NOT contain (>= x 0)
    HasNoIntConstraint = binary:match(QueryStr, <<"(>= x 0)">>) =:= nomatch,
    HasMainConstraint = binary:match(QueryStr, <<"(assert (> x 5))">>) =/= nomatch,

    case HasNoIntConstraint and HasMainConstraint of
        true ->
            io:format("✅ No constraint for Int~n"),
            ok;
        false ->
            io:format("❌ Unexpected constraint for Int, got: ~s~n", [QueryStr]),
            error(unexpected_int_constraint)
    end.

%% ============================================================================
%% Test: Mixed Nat and Int Variables
%% ============================================================================

test_mixed_nat_int_variables() ->
    io:format("Testing mixed Nat and Int variables... "),

    % Constraint: n + x > 10 (where n: Nat, x: Int)
    Constraint = #binary_op_expr{
        op = '>',
        left = #binary_op_expr{
            op = '+',
            left = #identifier_expr{name = n, location = #location{line = 1, column = 1}},
            right = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
            location = #location{line = 1, column = 1}
        },
        right = #literal_expr{value = 10, location = #location{line = 1, column = 1}},
        location = #location{line = 1, column = 1}
    },

    Env = #{n => {type, nat}, x => {type, int}},
    Query = cure_smt_translator:generate_query(Constraint, Env, #{}),
    QueryStr = iolist_to_binary(Query),

    % Check that query contains (>= n 0) but NOT (>= x 0)
    HasNatConstraint = binary:match(QueryStr, <<"(assert (>= n 0))">>) =/= nomatch,
    HasNoIntConstraint = binary:match(QueryStr, <<"(>= x 0)">>) =:= nomatch,

    case HasNatConstraint and HasNoIntConstraint of
        true ->
            io:format("✅ Correct constraints for mixed types~n"),
            ok;
        false ->
            io:format("❌ Wrong constraints for mixed types, got: ~s~n", [QueryStr]),
            error(wrong_mixed_constraints)
    end.

%% ============================================================================
%% Test: Nat in Formula
%% ============================================================================

test_nat_in_formula() ->
    io:format("Testing Nat variable in complex formula... "),

    % Constraint: forall n: Nat. n >= 0 => n + 1 > 0
    Body = #binary_op_expr{
        op = '=>',
        left = #binary_op_expr{
            op = '>=',
            left = #identifier_expr{name = n, location = #location{line = 1, column = 1}},
            right = #literal_expr{value = 0, location = #location{line = 1, column = 1}},
            location = #location{line = 1, column = 1}
        },
        right = #binary_op_expr{
            op = '>',
            left = #binary_op_expr{
                op = '+',
                left = #identifier_expr{name = n, location = #location{line = 1, column = 1}},
                right = #literal_expr{value = 1, location = #location{line = 1, column = 1}},
                location = #location{line = 1, column = 1}
            },
            right = #literal_expr{value = 0, location = #location{line = 1, column = 1}},
            location = #location{line = 1, column = 1}
        },
        location = #location{line = 1, column = 1}
    },

    Expr = #forall_expr{
        variables = [{n, nat}],
        body = Body,
        location = #location{line = 1, column = 1}
    },

    Query = cure_smt_translator:generate_query(Expr, #{}, #{}),
    QueryStr = iolist_to_binary(Query),

    % Should have logic LIA (quantified), forall, and the formula
    HasLogic = binary:match(QueryStr, <<"(set-logic LIA)">>) =/= nomatch,
    HasForall = binary:match(QueryStr, <<"(forall">>) =/= nomatch,

    case HasLogic and HasForall of
        true ->
            io:format("✅ Nat in quantified formula~n"),
            ok;
        false ->
            io:format("❌ Expected quantified formula, got: ~s~n", [QueryStr]),
            error(bad_quantified_formula)
    end.
