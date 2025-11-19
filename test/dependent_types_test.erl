-module(dependent_types_test).

-export([run/0]).

-include("../src/parser/cure_ast.hrl").

%% Test runner
run() ->
    io:format("~n=== Dependent Type Checking Test Suite ===~n~n"),

    Tests = [
        {"Check well-formed dependent type", fun test_check_dependent_type/0},
        {"Generate length constraint", fun test_generate_length_constraint/0},
        {"Generate bounds constraint", fun test_generate_bounds_constraint/0},
        {"Extend environment with value params", fun test_extend_env_value_params/0},
        {"Lookup value parameter", fun test_lookup_value_param/0},
        {"Check type-level operand (identifier)", fun test_check_type_level_operand_id/0},
        {"Check type-level operand (literal)", fun test_check_type_level_operand_lit/0},
        {"Instantiate dependent type", fun test_instantiate_dependent_type/0},
        {"Substitute value parameters", fun test_substitute_value_params/0},
        {"Is dependent type check", fun test_is_dependent_type/0}
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

test_check_dependent_type() ->
    % Test checking a well-formed dependent type: Vector(T, n: Nat)
    Type = #dependent_type{
        name = 'Vector',
        type_params = ['T'],
        value_params = [{n, {primitive_type, 'Nat', #location{}}}],
        location = #location{}
    },
    Env = #{},

    Result = cure_dependent_types:check_dependent_type(Type, Env),
    case Result of
        {ok, _} ->
            ok;
        _ ->
            error(
                {assertion_failed, {"Should successfully check dependent type", {result, Result}}}
            )
    end.

test_generate_length_constraint() ->
    % Test generating length(v) == n constraint
    VectorExpr = #identifier_expr{name = v, location = #location{}},
    LengthExpr = #identifier_expr{name = n, location = #location{}},

    Constraint = cure_dependent_types:generate_length_constraint(VectorExpr, LengthExpr),

    assert_is_record(Constraint, binary_op_expr, "Should be a binary operation"),
    assert_equals('==', Constraint#binary_op_expr.op, "Operator should be =="),

    % Check left side is length(v)
    LeftSide = Constraint#binary_op_expr.left,
    assert_is_record(LeftSide, function_call_expr, "Left side should be function call"),
    assert_equals(
        length,
        (LeftSide#function_call_expr.function)#identifier_expr.name,
        "Function should be length"
    ).

test_generate_bounds_constraint() ->
    % Test generating min <= x <= max constraint
    Expr = #identifier_expr{name = x, location = #location{}},
    MinExpr = #literal_expr{value = 0, location = #location{}},
    MaxExpr = #literal_expr{value = 100, location = #location{}},

    Constraint = cure_dependent_types:generate_bounds_constraint(Expr, {MinExpr, MaxExpr}),

    assert_is_record(Constraint, binary_op_expr, "Should be a binary operation"),
    assert_equals('and', Constraint#binary_op_expr.op, "Top operator should be 'and'"),

    % Check structure: (min <= x) and (x <= max)
    LeftPart = Constraint#binary_op_expr.left,
    RightPart = Constraint#binary_op_expr.right,
    assert_equals('<=', LeftPart#binary_op_expr.op, "Left part should be <="),
    assert_equals('<=', RightPart#binary_op_expr.op, "Right part should be <=").

test_extend_env_value_params() ->
    % Test extending environment with value parameters
    ValueParams = [{n, {primitive, nat}}, {m, {primitive, nat}}],
    Env = #{},

    NewEnv = cure_dependent_types:extend_env_with_value_params(ValueParams, Env),

    assert_true(maps:is_key(value_params, NewEnv), "Should have value_params key"),
    ValueParamsMap = maps:get(value_params, NewEnv),
    assert_true(maps:is_key(n, ValueParamsMap), "Should have n parameter"),
    assert_true(maps:is_key(m, ValueParamsMap), "Should have m parameter").

test_lookup_value_param() ->
    % Test looking up value parameters
    Env = #{value_params => #{n => {primitive, nat}, m => {primitive, nat}}},

    Result1 = cure_dependent_types:lookup_value_param(n, Env),
    case Result1 of
        {ok, _} -> ok;
        _ -> error({assertion_failed, {"Should find n parameter", {result, Result1}}})
    end,

    Result2 = cure_dependent_types:lookup_value_param(missing, Env),
    assert_equals(error, Result2, "Should return error for missing parameter").

test_check_type_level_operand_id() ->
    % Test checking identifier operand
    Operand = #identifier_expr{name = n, location = #location{}},
    Env = #{value_params => #{n => {primitive, nat}}},

    Result = cure_dependent_types:check_type_level_operand(Operand, Env),
    case Result of
        {ok, _, _} ->
            ok;
        _ ->
            error(
                {assertion_failed,
                    {"Should successfully check identifier operand", {result, Result}}}
            )
    end.

test_check_type_level_operand_lit() ->
    % Test checking literal operand
    Operand = #literal_expr{value = 42, location = #location{}},
    Env = #{},

    Result = cure_dependent_types:check_type_level_operand(Operand, Env),
    case Result of
        {ok, {primitive, nat}, _} ->
            ok;
        _ ->
            error(
                {assertion_failed, {"Should infer nat type for integer literal", {result, Result}}}
            )
    end.

test_instantiate_dependent_type() ->
    % Test instantiating Vector(T, n) with n = 5
    Type = #dependent_type{
        name = 'Vector',
        type_params = ['T'],
        value_params = [{n, #identifier_expr{name = n, location = #location{}}}],
        location = #location{}
    },
    Substitutions = [{n, #literal_expr{value = 5, location = #location{}}}],

    Result = cure_dependent_types:instantiate_dependent_type(Type, Substitutions),

    assert_is_record(Result, dependent_type, "Result should be dependent_type"),
    [{n, NewValue}] = Result#dependent_type.value_params,
    assert_is_record(NewValue, literal_expr, "Value should be substituted"),
    assert_equals(5, NewValue#literal_expr.value, "Value should be 5").

test_substitute_value_params() ->
    % Test substituting value parameters in a type
    Type = #dependent_type{
        name = 'Vector',
        type_params = ['T'],
        value_params = [{n, undefined}, {m, undefined}],
        location = #location{}
    },
    Substitutions = [{n, 10}, {m, 20}],

    Result = cure_dependent_types:substitute_value_params(Type, Substitutions),

    assert_is_record(Result, dependent_type, "Result should be dependent_type"),
    ValueParams = Result#dependent_type.value_params,
    assert_equals({n, 10}, lists:keyfind(n, 1, ValueParams), "n should be substituted"),
    assert_equals({m, 20}, lists:keyfind(m, 1, ValueParams), "m should be substituted").

test_is_dependent_type() ->
    % Test identifying dependent types
    DepType = #dependent_type{
        name = 'Vector',
        type_params = ['T'],
        value_params = [],
        location = #location{}
    },
    PrimType = {primitive, int},

    assert_true(
        cure_dependent_types:is_dependent_type(DepType),
        "Should identify dependent_type record"
    ),
    assert_false(
        cure_dependent_types:is_dependent_type(PrimType),
        "Should not identify primitive type as dependent"
    ).

%% ============================================================================
%% Helper Functions
%% ============================================================================

%% Assertion helpers
assert_equals(Expected, Actual, Message) ->
    case Expected =:= Actual of
        true -> ok;
        false -> error({assertion_failed, {Message, {expected, Expected}, {actual, Actual}}})
    end.

assert_matches({Tag, _}, {Tag, _}, _Message) ->
    ok;
assert_matches({Tag, _, _}, {Tag, _, _}, _Message) ->
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

assert_false(false, _Message) ->
    ok;
assert_false(true, Message) ->
    error({assertion_failed, {Message, {expected, false}, {actual, true}}}).

assert_is_record(Value, RecordName, Message) ->
    case is_record(Value, RecordName) of
        true ->
            ok;
        false ->
            error({assertion_failed, {Message, {expected_record, RecordName}, {actual, Value}}})
    end.
