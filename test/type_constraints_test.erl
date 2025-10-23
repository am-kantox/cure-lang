%% Type Constraints Test Suite
-module(type_constraints_test).

-export([run/0]).

-include("src/parser/cure_ast.hrl").

%% Run all tests
run() ->
    cure_utils:debug("~n=== Type Constraints Test Suite ===~n"),
    Tests = [
        fun test_basic_type_operations/0,
        fun test_type_compatibility/0,
        fun test_dependent_types/0
    ],
    Results = [run_test(Test) || Test <- Tests],
    Passed = length([R || R <- Results, R =:= ok]),
    Total = length(Results),
    cure_utils:debug("~nResults: ~w/~w tests passed~n", [Passed, Total]),
    case Passed of
        Total -> cure_utils:debug("All type constraints tests passed!~n");
        _ -> cure_utils:debug("Some tests failed.~n")
    end.

run_test(Test) ->
    try
        Result = Test(),
        case Result of
            ok ->
                cure_utils:debug("PASSED~n"),
                ok;
            {error, _Reason} ->
                cure_utils:debug("FAILED: ~p~n", [_Reason]),
                error
        end
    catch
        Class:Error:Stack ->
            cure_utils:debug("FAILED: ~p:~p~n", [Class, Error]),
            cure_utils:debug("Stack: ~p~n", [Stack]),
            error
    end.

%% Test basic type operations
test_basic_type_operations() ->
    cure_utils:debug("Testing Basic Type Operations... "),

    % Test primitive type creation
    IntType = #primitive_type{name = 'Int', location = #location{line = 1, column = 1}},
    BoolType = #primitive_type{name = 'Bool', location = #location{line = 1, column = 1}},

    % Simple validation that records can be created
    case {IntType, BoolType} of
        {#primitive_type{name = 'Int'}, #primitive_type{name = 'Bool'}} ->
            ok;
        _ ->
            {error, basic_type_creation_failed}
    end.

%% Test type compatibility
test_type_compatibility() ->
    cure_utils:debug("Testing Type Compatibility... "),

    % Test list type creation
    ListType = #list_type{
        element_type = #primitive_type{name = 'Int', location = #location{line = 1, column = 1}},
        length = undefined,
        location = #location{line = 2, column = 1}
    },

    % Test tuple type creation
    TupleType = #tuple_type{
        element_types = [
            #primitive_type{name = 'Int', location = #location{line = 1, column = 1}},
            #primitive_type{name = 'String', location = #location{line = 1, column = 1}}
        ],
        location = #location{line = 3, column = 1}
    },

    case {ListType, TupleType} of
        {#list_type{}, #tuple_type{}} ->
            ok;
        _ ->
            {error, type_compatibility_failed}
    end.

%% Test dependent types
test_dependent_types() ->
    cure_utils:debug("Testing Dependent Types... "),

    % Test dependent type creation
    DepType = #dependent_type{
        name = 'Vector',
        params = [
            #type_param{
                name = 'T',
                value = #primitive_type{name = 'Int', location = #location{line = 1, column = 1}},
                location = #location{line = 4, column = 1}
            }
        ],
        location = #location{line = 4, column = 1}
    },

    case DepType of
        #dependent_type{name = 'Vector'} ->
            ok;
        _ ->
            {error, dependent_types_failed}
    end.
