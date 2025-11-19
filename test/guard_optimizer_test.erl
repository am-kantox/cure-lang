-module(guard_optimizer_test).

-export([run/0]).

-include("../src/parser/cure_ast.hrl").

%% Test runner
run() ->
    io:format("~n=== Guard Optimizer Test Suite ===~n~n"),

    Tests = [
        {"Guard implication: n > 10 implies n > 5", fun test_basic_implication/0},
        {"Guard implication: n > 5 does not imply n > 10", fun test_non_implication/0},
        {"Guard implication: n >= 10 implies n > 5", fun test_ge_implies_gt/0},
        {"Guard implication: n == 10 implies n > 5", fun test_eq_implies_gt/0},
        {"Redundant guard detection", fun test_redundant_detection/0},
        {"Guard optimization: remove redundant guards", fun test_optimize_guards/0},
        {"Nested guard optimization", fun test_nested_guards/0},
        {"Guard ordering by specificity", fun test_guard_ordering/0},
        {"Guard simplification: double negation", fun test_simplify_double_negation/0},
        {"Guard simplification: AND with true", fun test_simplify_and_true/0},
        {"Guard simplification: AND with false", fun test_simplify_and_false/0},
        {"Guard simplification: OR with true", fun test_simplify_or_true/0},
        {"Guard simplification: OR with false", fun test_simplify_or_false/0},
        {"Conjunction implication: (n > 10 and n < 20) implies n > 5",
            fun test_conjunction_implication/0},
        {"Guard specificity scoring", fun test_specificity_scoring/0}
    ],

    Results = lists:map(
        fun({TestName, TestFun}) ->
            io:format("Running: ~s... ", [TestName]),
            try
                TestFun(),
                io:format("✓ PASS~n"),
                {pass, TestName}
            catch
                error:{assertion_failed, Reason} ->
                    io:format("✗ FAIL: ~p~n", [Reason]),
                    {fail, TestName, Reason};
                Class:Error:Stack ->
                    io:format("✗ ERROR: ~p:~p~n~p~n", [Class, Error, Stack]),
                    {error, TestName, {Class, Error}}
            end
        end,
        Tests
    ),

    Passed = length([R || {pass, _} = R <- Results]),
    Failed = length([R || {fail, _, _} = R <- Results]),
    Errors = length([R || {error, _, _} = R <- Results]),
    Total = length(Tests),

    io:format("~n=== Results ===~n"),
    io:format("Passed: ~p/~p~n", [Passed, Total]),
    io:format("Failed: ~p/~p~n", [Failed, Total]),
    io:format("Errors: ~p/~p~n", [Errors, Total]),

    if
        Passed =:= Total ->
            io:format("~n✓ All tests passed!~n"),
            halt(0);
        true ->
            io:format("~n✗ Some tests failed.~n"),
            halt(1)
    end.

%% ============================================================================
%% Test Cases
%% ============================================================================

test_basic_implication() ->
    % n > 10 implies n > 5
    Guard1 = make_comparison('>', "n", 10),
    Guard2 = make_comparison('>', "n", 5),

    Result = cure_guard_optimizer:check_guard_implication(Guard1, Guard2),
    assert_equals({implies, true}, Result, "n > 10 should imply n > 5").

test_non_implication() ->
    % n > 5 does NOT imply n > 10
    Guard1 = make_comparison('>', "n", 5),
    Guard2 = make_comparison('>', "n", 10),

    Result = cure_guard_optimizer:check_guard_implication(Guard1, Guard2),
    assert_equals({implies, false}, Result, "n > 5 should not imply n > 10").

test_ge_implies_gt() ->
    % n >= 10 implies n > 5
    Guard1 = make_comparison('>=', "n", 10),
    Guard2 = make_comparison('>', "n", 5),

    Result = cure_guard_optimizer:check_guard_implication(Guard1, Guard2),
    assert_equals({implies, true}, Result, "n >= 10 should imply n > 5").

test_eq_implies_gt() ->
    % n == 10 implies n > 5
    Guard1 = make_comparison('==', "n", 10),
    Guard2 = make_comparison('>', "n", 5),

    Result = cure_guard_optimizer:check_guard_implication(Guard1, Guard2),
    assert_equals({implies, true}, Result, "n == 10 should imply n > 5").

test_redundant_detection() ->
    Guard1 = make_comparison('>', "n", 10),
    % Redundant
    Guard2 = make_comparison('>', "n", 5),

    Result = cure_guard_optimizer:is_guard_redundant(Guard1, Guard2),
    case Result of
        {redundant, _} ->
            ok;
        _ ->
            error(
                {assertion_failed,
                    {"Guard2 should be redundant given Guard1", {expected, redundant},
                        {actual, Result}}}
            )
    end.

test_optimize_guards() ->
    Guards = [
        % Keep
        make_comparison('>', "n", 10),
        % Redundant - remove
        make_comparison('>', "n", 5),
        % Redundant - remove
        make_comparison('>', "n", 0)
    ],

    Optimized = cure_guard_optimizer:optimize_guards(Guards),

    % Should keep only the first guard
    assert_equals(1, length(Optimized), "Should keep only one non-redundant guard").

test_nested_guards() ->
    % Test match clauses with redundant guards
    % match x with
    % | n when n > 10 -> ...  (Guard 1)
    % | n when n > 5 -> ...  (Guard 2 - independent but related)
    % | n when n > 10 -> ... (Guard 3 - redundant with Guard 1)

    Guard1 = make_comparison('>', "n", 10),
    Guard2 = make_comparison('>', "n", 5),
    % Redundant with Guard1
    Guard3 = make_comparison('>', "n", 10),

    Clause1 = #match_clause{
        pattern = make_identifier("n"),
        guard = Guard1,
        body = make_literal(1),
        location = #location{}
    },
    Clause2 = #match_clause{
        pattern = make_identifier("n"),
        guard = Guard2,
        body = make_literal(2),
        location = #location{}
    },
    Clause3 = #match_clause{
        pattern = make_identifier("n"),
        % This is redundant given Guard1
        guard = Guard3,
        body = make_literal(3),
        location = #location{}
    },

    Clauses = [Clause1, Clause2, Clause3],
    Optimized = cure_guard_optimizer:optimize_nested_guards(Clauses),

    % Should have 3 clauses still, but Clause3 guard should be simplified to true
    assert_equals(3, length(Optimized), "Should maintain all clauses"),

    % Extract third clause and check its guard
    [_, _, OptClause3] = Optimized,
    #match_clause{guard = OptGuard3} = OptClause3,

    % Guard3 should be simplified to true since it's redundant
    assert_equals(
        #literal_expr{value = true, location = #location{}},
        OptGuard3,
        "Redundant guard should be simplified to true"
    ).

test_guard_ordering() ->
    % Create guards with different specificity

    % Less specific
    Guard1 = make_comparison('>', "n", 0),
    % More specific
    Guard2 = make_comparison('>', "n", 10),
    % Most specific (equality)
    Guard3 = make_comparison('==', "n", 5),

    GuardsWithBodies = [
        {Guard1, body1},
        {Guard2, body2},
        {Guard3, body3}
    ],

    Ordered = cure_guard_optimizer:order_guards_by_specificity(GuardsWithBodies),

    % Should be ordered: Guard3 (==), Guard2 (> 10), Guard1 (> 0)
    [{FirstGuard, _}, _, _] = Ordered,

    % Check that equality comes first (most specific)
    #binary_op_expr{op = FirstOp} = FirstGuard,
    assert_equals('==', FirstOp, "Equality guard should come first").

test_simplify_double_negation() ->
    % not (not x) => x
    X = make_identifier("x"),
    DoubleNeg = #unary_op_expr{
        op = 'not',
        operand = #unary_op_expr{
            op = 'not',
            operand = X,
            location = #location{}
        },
        location = #location{}
    },

    Simplified = cure_guard_optimizer:simplify_guard(DoubleNeg),
    assert_equals(X, Simplified, "Double negation should simplify to original expression").

test_simplify_and_true() ->
    % x and true => x
    X = make_identifier("x"),
    AndTrue = #binary_op_expr{
        op = 'and',
        left = X,
        right = make_literal(true),
        location = #location{}
    },

    Simplified = cure_guard_optimizer:simplify_guard(AndTrue),
    assert_equals(X, Simplified, "x and true should simplify to x").

test_simplify_and_false() ->
    % x and false => false
    X = make_identifier("x"),
    False = make_literal(false),
    AndFalse = #binary_op_expr{
        op = 'and',
        left = X,
        right = False,
        location = #location{}
    },

    Simplified = cure_guard_optimizer:simplify_guard(AndFalse),
    assert_equals(False, Simplified, "x and false should simplify to false").

test_simplify_or_true() ->
    % x or true => true
    X = make_identifier("x"),
    True = make_literal(true),
    OrTrue = #binary_op_expr{
        op = 'or',
        left = X,
        right = True,
        location = #location{}
    },

    Simplified = cure_guard_optimizer:simplify_guard(OrTrue),
    assert_equals(True, Simplified, "x or true should simplify to true").

test_simplify_or_false() ->
    % x or false => x
    X = make_identifier("x"),
    OrFalse = #binary_op_expr{
        op = 'or',
        left = X,
        right = make_literal(false),
        location = #location{}
    },

    Simplified = cure_guard_optimizer:simplify_guard(OrFalse),
    assert_equals(X, Simplified, "x or false should simplify to x").

test_conjunction_implication() ->
    % (n > 10 and n < 20) implies n > 5
    Guard1 = #binary_op_expr{
        op = 'and',
        left = make_comparison('>', "n", 10),
        right = make_comparison('<', "n", 20),
        location = #location{}
    },
    Guard2 = make_comparison('>', "n", 5),

    Result = cure_guard_optimizer:check_guard_implication(Guard1, Guard2),
    assert_equals({implies, true}, Result, "(n > 10 and n < 20) should imply n > 5").

test_specificity_scoring() ->
    % Test that specificity scoring works correctly

    % Score: 10
    GuardEq = make_comparison('==', "n", 10),
    % Score: 5
    GuardGt10 = make_comparison('>', "n", 10),
    % Score: 5
    _GuardGt0 = make_comparison('>', "n", 0),
    % Score: 2
    GuardNe = make_comparison('/=', "n", 5),

    ScoreEq = cure_guard_optimizer:guard_specificity(GuardEq),
    ScoreGt10 = cure_guard_optimizer:guard_specificity(GuardGt10),
    ScoreNe = cure_guard_optimizer:guard_specificity(GuardNe),

    assert_true(ScoreEq > ScoreGt10, "Equality should be more specific than >"),
    assert_true(ScoreGt10 > ScoreNe, "> should be more specific than /=").

%% ============================================================================
%% Helper Functions
%% ============================================================================

make_comparison(Op, VarName, Value) ->
    #binary_op_expr{
        op = Op,
        left = make_identifier(VarName),
        right = make_literal(Value),
        location = #location{}
    }.

make_identifier(Name) ->
    #identifier_expr{
        name = list_to_atom(Name),
        location = #location{}
    }.

make_literal(Value) ->
    #literal_expr{
        type = Value,
        location = #location{}
    }.

%% Assertion helpers
assert_equals(Expected, Actual, Message) ->
    case Expected =:= Actual of
        true -> ok;
        false -> error({assertion_failed, {Message, {expected, Expected}, {actual, Actual}}})
    end.

assert_matches({Tag, _}, {Tag, _}, _Message) ->
    ok;
assert_matches(Pattern, Value, Message) ->
    case Pattern =:= Value of
        true -> ok;
        false -> error({assertion_failed, {Message, {pattern, Pattern}, {value, Value}}})
    end.

assert_true(true, _Message) ->
    ok;
assert_true(false, Message) ->
    error({assertion_failed, {Message, {expected, true}, {actual, false}}}).
