-module(dependent_parser_test).

-export([run/0]).

-include("../src/parser/cure_ast.hrl").

%% Test runner
run() ->
    io:format("~n=== Dependent Type Parser Test Suite ===~n~n"),

    Tests = [
        {"Parse type parameter (type)", fun test_parse_type_param/0},
        {"Parse value parameter (n: Nat)", fun test_parse_value_param_simple/0},
        {"Parse constrained value parameter (n: Nat where n > 0)",
            fun test_parse_value_param_constrained/0},
        {"Identify type-level operators", fun test_is_type_level_op/0},
        {"Parse type-level expression (m + n)", fun test_parse_type_level_addition/0},
        {"Parse type-level comparison (i < n)", fun test_parse_type_level_comparison/0},
        {"Create dependent type record", fun test_make_dependent_type/0},
        {"Create dependent function type", fun test_make_dependent_function_type/0},
        {"Create type-level expression", fun test_make_type_level_expr/0},
        {"Check if value parameter", fun test_is_value_param/0}
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

test_parse_type_param() ->
    % Parse a type parameter like T
    Input = {type_param, 'T', undefined, #location{}},
    Result = cure_dependent_parser:parse_type_params([Input]),

    [TypeParam] = Result,
    assert_equals('T', TypeParam#type_param.name, "Type parameter name should be T"),
    assert_equals(type, TypeParam#type_param.kind, "Kind should be 'type'"),
    assert_equals(
        undefined, TypeParam#type_param.type, "Type should be undefined for type parameters"
    ).

test_parse_value_param_simple() ->
    % Parse a value parameter like n: Nat
    Input = {type_param, n, {primitive_type, 'Nat', #location{}}, #location{}},
    Result = cure_dependent_parser:parse_type_params([Input]),

    [ValueParam] = Result,
    assert_equals(n, ValueParam#type_param.name, "Value parameter name should be n"),
    assert_equals(value, ValueParam#type_param.kind, "Kind should be 'value'"),
    assert_not_equals(
        undefined, ValueParam#type_param.type, "Type should be defined for value parameters"
    ).

test_parse_value_param_constrained() ->
    % Parse a constrained value parameter like n: Nat where n > 0
    Constraint = #binary_op_expr{
        op = '>',
        left = #identifier_expr{name = n, location = #location{}},
        right = #literal_expr{value = 0, location = #location{}},
        location = #location{}
    },
    Input = {type_param, n, {primitive_type, 'Nat', #location{}}, Constraint, #location{}},
    Result = cure_dependent_parser:parse_type_params([Input]),

    [ValueParam] = Result,
    assert_equals(n, ValueParam#type_param.name, "Value parameter name should be n"),
    assert_equals(value, ValueParam#type_param.kind, "Kind should be 'value'"),
    assert_not_equals(undefined, ValueParam#type_param.constraint, "Constraint should be defined").

test_is_type_level_op() ->
    % Test operator recognition
    assert_true(cure_dependent_parser:is_type_level_op('+'), "+ is a type-level operator"),
    assert_true(cure_dependent_parser:is_type_level_op('-'), "- is a type-level operator"),
    assert_true(cure_dependent_parser:is_type_level_op('*'), "* is a type-level operator"),
    assert_true(cure_dependent_parser:is_type_level_op('/'), "/ is a type-level operator"),
    assert_true(cure_dependent_parser:is_type_level_op('=='), "== is a type-level operator"),
    assert_true(cure_dependent_parser:is_type_level_op('<'), "< is a type-level operator"),
    assert_true(cure_dependent_parser:is_type_level_op('<='), "<= is a type-level operator"),
    assert_true(cure_dependent_parser:is_type_level_op('and'), "and is a type-level operator"),
    assert_false(cure_dependent_parser:is_type_level_op('++'), "++ is not a type-level operator"),
    assert_false(cure_dependent_parser:is_type_level_op('|>'), "|> is not a type-level operator").

test_parse_type_level_addition() ->
    % Parse m + n
    Input = #binary_op_expr{
        op = '+',
        left = #identifier_expr{name = m, location = #location{}},
        right = #identifier_expr{name = n, location = #location{}},
        location = #location{}
    },

    Result = cure_dependent_parser:parse_type_level_expr(Input),

    assert_is_record(Result, type_level_expr, "Result should be a type_level_expr"),
    assert_equals('+', Result#type_level_expr.op, "Operator should be +"),
    assert_equals(
        m, (Result#type_level_expr.left)#identifier_expr.name, "Left operand should be m"
    ),
    assert_equals(
        n, (Result#type_level_expr.right)#identifier_expr.name, "Right operand should be n"
    ).

test_parse_type_level_comparison() ->
    % Parse i < n
    Input = #binary_op_expr{
        op = '<',
        left = #identifier_expr{name = i, location = #location{}},
        right = #identifier_expr{name = n, location = #location{}},
        location = #location{}
    },

    Result = cure_dependent_parser:parse_type_level_expr(Input),

    assert_is_record(Result, type_level_expr, "Result should be a type_level_expr"),
    assert_equals('<', Result#type_level_expr.op, "Operator should be <"),
    assert_equals(
        i, (Result#type_level_expr.left)#identifier_expr.name, "Left operand should be i"
    ),
    assert_equals(
        n, (Result#type_level_expr.right)#identifier_expr.name, "Right operand should be n"
    ).

test_make_dependent_type() ->
    % Create Vector(T, n: Nat)
    Result = cure_dependent_parser:make_dependent_type(
        'Vector',
        ['T'],
        [{n, {primitive_type, 'Nat', #location{}}}],
        #location{}
    ),

    assert_is_record(Result, dependent_type, "Result should be a dependent_type"),
    assert_equals('Vector', Result#dependent_type.name, "Type name should be Vector"),
    assert_equals(['T'], Result#dependent_type.type_params, "Should have type parameter T"),
    assert_equals(1, length(Result#dependent_type.value_params), "Should have one value parameter").

test_make_dependent_function_type() ->
    % Create function type: <T, n: Nat>(v: Vector(T, n)) -> T
    TypeParams = [
        #type_param{
            name = 'T',
            kind = type,
            type = undefined,
            constraint = undefined,
            location = #location{}
        },
        #type_param{
            name = n,
            kind = value,
            type = {primitive_type, 'Nat', #location{}},
            constraint = undefined,
            location = #location{}
        }
    ],
    Params = [
        #param{
            name = v,
            type = {dependent_type, 'Vector', ['T'], [{n, undefined}], #location{}},
            location = #location{}
        }
    ],
    ReturnType = {primitive_type, 'T', #location{}},

    Result = cure_dependent_parser:make_dependent_function_type(
        TypeParams,
        Params,
        ReturnType,
        [],
        #location{}
    ),

    assert_is_record(Result, dependent_function_type, "Result should be a dependent_function_type"),
    assert_equals(
        2, length(Result#dependent_function_type.type_params), "Should have 2 type parameters"
    ),
    assert_equals(
        1, length(Result#dependent_function_type.params), "Should have 1 function parameter"
    ).

test_make_type_level_expr() ->
    % Create m + n expression
    Result = cure_dependent_parser:make_type_level_expr(
        '+',
        #identifier_expr{name = m, location = #location{}},
        #identifier_expr{name = n, location = #location{}},
        #location{}
    ),

    assert_is_record(Result, type_level_expr, "Result should be a type_level_expr"),
    assert_equals('+', Result#type_level_expr.op, "Operator should be +").

test_is_value_param() ->
    % Test value parameter identification
    ValueParam = {param, n, {primitive_type, 'Nat', #location{}}, #location{}},
    TypeParam = {param, 'T', undefined, #location{}},

    assert_true(
        cure_dependent_parser:is_value_param(ValueParam),
        "Parameter with type should be identified as value parameter"
    ),
    assert_false(
        cure_dependent_parser:is_value_param(TypeParam),
        "Parameter without type should not be identified as value parameter"
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

assert_not_equals(NotExpected, Actual, Message) ->
    case NotExpected =/= Actual of
        true -> ok;
        false -> error({assertion_failed, {Message, {not_expected, NotExpected}, {actual, Actual}}})
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
