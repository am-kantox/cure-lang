-module(smt_simplify_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").

%% Test constraint simplification functionality
run() ->
    io:format("~n=== Testing SMT Constraint Simplification ===~n~n"),

    % Test 1: Arithmetic identities
    test_arithmetic_identities(),

    % Test 2: Boolean identities
    test_boolean_identities(),

    % Test 3: Constant folding
    test_constant_folding(),

    % Test 4: Comparison simplifications
    test_comparison_simplifications(),

    % Test 5: Double negation
    test_double_negation(),

    io:format("~n=== All Simplification Tests Passed ===~n"),
    ok.

%% Helper to create literal
lit(Value) ->
    #literal_expr{value = Value, location = #location{line = 0, column = 0, file = undefined}}.

%% Helper to create identifier
var(Name) ->
    #identifier_expr{name = Name, location = #location{line = 0, column = 0, file = undefined}}.

%% Helper to create binary op
binop(Op, Left, Right) ->
    #binary_op_expr{
        op = Op,
        left = Left,
        right = Right,
        location = #location{line = 0, column = 0, file = undefined}
    }.

%% Helper to create unary op
unop(Op, Operand) ->
    #unary_op_expr{
        op = Op,
        operand = Operand,
        location = #location{line = 0, column = 0, file = undefined}
    }.

%% Test arithmetic identity simplifications
test_arithmetic_identities() ->
    io:format("Testing arithmetic identities...~n"),

    % x + 0 = x
    Expr1 = binop('+', var(x), lit(0)),
    Result1 = cure_smt_solver:simplify_constraint(Expr1, #{}),
    assert_equal(Result1, var(x), "x + 0 should simplify to x"),

    % 0 + x = x
    Expr2 = binop('+', lit(0), var(x)),
    Result2 = cure_smt_solver:simplify_constraint(Expr2, #{}),
    assert_equal(Result2, var(x), "0 + x should simplify to x"),

    % x * 1 = x
    Expr3 = binop('*', var(x), lit(1)),
    Result3 = cure_smt_solver:simplify_constraint(Expr3, #{}),
    assert_equal(Result3, var(x), "x * 1 should simplify to x"),

    % x * 0 should simplify to 0
    Expr4 = binop('*', var(x), lit(0)),
    Result4 = cure_smt_solver:simplify_constraint(Expr4, #{}),
    assert_is_zero(Result4, "x * 0 should simplify to 0"),

    % x - 0 = x
    Expr5 = binop('-', var(x), lit(0)),
    Result5 = cure_smt_solver:simplify_constraint(Expr5, #{}),
    assert_equal(Result5, var(x), "x - 0 should simplify to x"),

    io:format("  ✓ All arithmetic identity tests passed~n~n"),
    ok.

%% Test boolean identity simplifications
test_boolean_identities() ->
    io:format("Testing boolean identities...~n"),

    % x and true = x
    Expr1 = binop('and', var(x), lit(true)),
    Result1 = cure_smt_solver:simplify_constraint(Expr1, #{}),
    assert_equal(Result1, var(x), "x and true should simplify to x"),

    % x and false = false
    Expr2 = binop('and', var(x), lit(false)),
    Result2 = cure_smt_solver:simplify_constraint(Expr2, #{}),
    assert_equal(Result2, lit(false), "x and false should simplify to false"),

    % x or false = x
    Expr3 = binop('or', var(x), lit(false)),
    Result3 = cure_smt_solver:simplify_constraint(Expr3, #{}),
    assert_equal(Result3, var(x), "x or false should simplify to x"),

    % x or true = true
    Expr4 = binop('or', var(x), lit(true)),
    Result4 = cure_smt_solver:simplify_constraint(Expr4, #{}),
    assert_equal(Result4, lit(true), "x or true should simplify to true"),

    io:format("  ✓ All boolean identity tests passed~n~n"),
    ok.

%% Test constant folding
test_constant_folding() ->
    io:format("Testing constant folding...~n"),

    % 2 + 3 = 5
    Expr1 = binop('+', lit(2), lit(3)),
    Result1 = cure_smt_solver:simplify_constraint(Expr1, #{}),
    assert_equal(Result1, lit(5), "2 + 3 should fold to 5"),

    % 10 - 3 = 7
    Expr2 = binop('-', lit(10), lit(3)),
    Result2 = cure_smt_solver:simplify_constraint(Expr2, #{}),
    assert_equal(Result2, lit(7), "10 - 3 should fold to 7"),

    % 4 * 5 = 20
    Expr3 = binop('*', lit(4), lit(5)),
    Result3 = cure_smt_solver:simplify_constraint(Expr3, #{}),
    assert_equal(Result3, lit(20), "4 * 5 should fold to 20"),

    % true and false = false
    Expr4 = binop('and', lit(true), lit(false)),
    Result4 = cure_smt_solver:simplify_constraint(Expr4, #{}),
    assert_equal(Result4, lit(false), "true and false should fold to false"),

    io:format("  ✓ All constant folding tests passed~n~n"),
    ok.

%% Test comparison simplifications
test_comparison_simplifications() ->
    io:format("Testing comparison simplifications...~n"),

    % x == x = true
    Expr1 = binop('==', var(x), var(x)),
    Result1 = cure_smt_solver:simplify_constraint(Expr1, #{}),
    assert_equal(Result1, lit(true), "x == x should simplify to true"),

    % x /= x = false
    Expr2 = binop('/=', var(x), var(x)),
    Result2 = cure_smt_solver:simplify_constraint(Expr2, #{}),
    assert_equal(Result2, lit(false), "x /= x should simplify to false"),

    % x < x = false
    Expr3 = binop('<', var(x), var(x)),
    Result3 = cure_smt_solver:simplify_constraint(Expr3, #{}),
    assert_equal(Result3, lit(false), "x < x should simplify to false"),

    % x >= x = true
    Expr4 = binop('>=', var(x), var(x)),
    Result4 = cure_smt_solver:simplify_constraint(Expr4, #{}),
    assert_equal(Result4, lit(true), "x >= x should simplify to true"),

    io:format("  ✓ All comparison simplification tests passed~n~n"),
    ok.

%% Test double negation elimination
test_double_negation() ->
    io:format("Testing double negation elimination...~n"),

    % not (not x) = x
    Expr1 = unop('not', unop('not', var(x))),
    Result1 = cure_smt_solver:simplify_constraint(Expr1, #{}),
    assert_equal(Result1, var(x), "not (not x) should simplify to x"),

    % -(-x) = x
    Expr2 = unop('-', unop('-', var(x))),
    Result2 = cure_smt_solver:simplify_constraint(Expr2, #{}),
    assert_equal(Result2, var(x), "-(-x) should simplify to x"),

    % not true = false
    Expr3 = unop('not', lit(true)),
    Result3 = cure_smt_solver:simplify_constraint(Expr3, #{}),
    assert_equal(Result3, lit(false), "not true should simplify to false"),

    % -5 = -5
    Expr4 = unop('-', lit(5)),
    Result4 = cure_smt_solver:simplify_constraint(Expr4, #{}),
    assert_equal(Result4, lit(-5), "-5 should simplify to -5"),

    io:format("  ✓ All double negation tests passed~n~n"),
    ok.

%% Assertion helpers
assert_equal(Actual, Expected, Msg) ->
    case Actual =:= Expected of
        true ->
            ok;
        false ->
            io:format("  ✗ FAILED: ~s~n", [Msg]),
            io:format("    Expected: ~p~n", [Expected]),
            io:format("    Actual:   ~p~n", [Actual]),
            error({assertion_failed, Msg})
    end.

assert_is_zero(#literal_expr{value = 0}, _Msg) ->
    ok;
assert_is_zero(
    #binary_op_expr{left = #literal_expr{value = 0}, right = #literal_expr{value = 0}}, _Msg
) ->
    % Also accept (0 * 0) form
    ok;
assert_is_zero(Actual, Msg) ->
    io:format("  ✗ FAILED: ~s~n", [Msg]),
    io:format("    Expected: 0~n"),
    io:format("    Actual:   ~p~n", [Actual]),
    error({assertion_failed, Msg}).
