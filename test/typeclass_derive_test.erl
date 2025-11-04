-module(typeclass_derive_test).

-include("../src/parser/cure_ast.hrl").
-export([run/0]).

%% ============================================================================
%% Test Runner
%% ============================================================================

run() ->
    io:format("=== Running Typeclass Derivation Tests ===~n~n"),

    Tests = [
        {"Derive Show for primitive type", fun test_derive_show_primitive/0},
        {"Derive Show for record type", fun test_derive_show_record/0},
        {"Derive Eq for primitive type", fun test_derive_eq_primitive/0},
        {"Derive Eq for record type", fun test_derive_eq_record/0},
        {"Derive Ord for record type", fun test_derive_ord_record/0},
        {"Can derive check", fun test_can_derive/0},
        {"Cannot derive unsupported typeclass", fun test_cannot_derive_unsupported/0},
        {"Field constraints for Show", fun test_field_constraints_show/0},
        {"Field constraints for parameterized type", fun test_field_constraints_parameterized/0}
    ],

    Results = run_tests(Tests, [], 0, 0),

    io:format("~n=== Test Summary ===~n"),
    io:format(
        "Total: ~p, Passed: ~p, Failed: ~p~n",
        [length(Tests), element(1, Results), element(2, Results)]
    ),

    case element(2, Results) of
        0 -> io:format("~nAll tests passed!~n");
        _ -> io:format("~nSome tests failed.~n")
    end.

run_tests([], _Acc, Passed, Failed) ->
    {Passed, Failed};
run_tests([{Name, TestFun} | Rest], Acc, Passed, Failed) ->
    io:format("Running: ~s ... ", [Name]),
    try
        TestFun(),
        io:format("PASSED~n"),
        run_tests(Rest, Acc, Passed + 1, Failed)
    catch
        Error:Reason:Stacktrace ->
            io:format("FAILED~n"),
            io:format("  Error: ~p~n  Reason: ~p~n", [Error, Reason]),
            io:format("  Stack: ~p~n", [Stacktrace]),
            run_tests(Rest, Acc, Passed, Failed + 1)
    end.

%% ============================================================================
%% Test Cases
%% ============================================================================

test_derive_show_primitive() ->
    Location = #location{line = 1, column = 1, file = "test.cure"},
    IntType = #primitive_type{name = 'Int', location = Location},

    Result = cure_derive:derive_instance('Show', IntType, [], undefined),

    case Result of
        {ok, #instance_def{typeclass = 'Show', type_args = [#primitive_type{name = 'Int'}]}} ->
            ok;
        Other ->
            throw({unexpected_result, Other})
    end.

test_derive_show_record() ->
    Location = #location{line = 1, column = 1, file = "test.cure"},

    Fields = [
        #record_field_def{
            name = name,
            type = #primitive_type{name = 'String', location = Location},
            location = Location
        },
        #record_field_def{
            name = age,
            type = #primitive_type{name = 'Int', location = Location},
            location = Location
        }
    ],

    RecordDef = #record_def{
        name = 'Person',
        fields = Fields,
        location = Location
    },

    Result = cure_derive:derive_instance('Show', RecordDef, [], undefined),

    case Result of
        {ok, #instance_def{
            typeclass = 'Show',
            type_args = [#primitive_type{name = 'Person'}],
            methods = [#function_def{name = show}]
        }} ->
            ok;
        Other ->
            throw({unexpected_result, Other})
    end.

test_derive_eq_primitive() ->
    Location = #location{line = 1, column = 1, file = "test.cure"},
    BoolType = #primitive_type{name = 'Bool', location = Location},

    Result = cure_derive:derive_instance('Eq', BoolType, [], undefined),

    case Result of
        {ok, #instance_def{
            typeclass = 'Eq',
            type_args = [#primitive_type{name = 'Bool'}],
            methods = [#function_def{name = '=='}]
        }} ->
            ok;
        Other ->
            throw({unexpected_result, Other})
    end.

test_derive_eq_record() ->
    Location = #location{line = 1, column = 1, file = "test.cure"},

    Fields = [
        #record_field_def{
            name = x,
            type = #primitive_type{name = 'Int', location = Location},
            location = Location
        },
        #record_field_def{
            name = y,
            type = #primitive_type{name = 'Int', location = Location},
            location = Location
        }
    ],

    RecordDef = #record_def{
        name = 'Point',
        fields = Fields,
        location = Location
    },

    Result = cure_derive:derive_instance('Eq', RecordDef, [], undefined),

    case Result of
        {ok, #instance_def{
            typeclass = 'Eq',
            type_args = [#primitive_type{name = 'Point'}],
            methods = [#function_def{name = '=='}]
        }} ->
            ok;
        Other ->
            throw({unexpected_result, Other})
    end.

test_derive_ord_record() ->
    Location = #location{line = 1, column = 1, file = "test.cure"},

    Fields = [
        #record_field_def{
            name = x,
            type = #primitive_type{name = 'Int', location = Location},
            location = Location
        }
    ],

    RecordDef = #record_def{
        name = 'Value',
        fields = Fields,
        location = Location
    },

    Result = cure_derive:derive_instance('Ord', RecordDef, [], undefined),

    case Result of
        {ok, #instance_def{
            typeclass = 'Ord',
            type_args = [#primitive_type{name = 'Value'}],
            methods = [#function_def{name = compare}],
            constraints = Constraints
        }} ->
            % Ord should include Eq constraint
            case
                lists:any(
                    fun(#typeclass_constraint{typeclass = TC}) -> TC =:= 'Eq' end,
                    Constraints
                )
            of
                true -> ok;
                false -> throw(missing_eq_constraint)
            end;
        Other ->
            throw({unexpected_result, Other})
    end.

test_can_derive() ->
    Location = #location{line = 1, column = 1, file = "test.cure"},

    RecordDef = #record_def{
        name = 'Test',
        fields = [],
        location = Location
    },

    true = cure_derive:can_derive('Show', RecordDef),
    true = cure_derive:can_derive('Eq', RecordDef),
    true = cure_derive:can_derive('Ord', RecordDef),
    false = cure_derive:can_derive('Functor', RecordDef),

    ok.

test_cannot_derive_unsupported() ->
    Location = #location{line = 1, column = 1, file = "test.cure"},
    IntType = #primitive_type{name = 'Int', location = Location},

    Result = cure_derive:derive_instance('Functor', IntType, [], undefined),

    case Result of
        {error, {cannot_derive, 'Functor'}} ->
            ok;
        Other ->
            throw({unexpected_result, Other})
    end.

test_field_constraints_show() ->
    Location = #location{line = 1, column = 1, file = "test.cure"},

    % Record with no parameterized fields - should have no constraints
    Fields1 = [
        #record_field_def{
            name = x,
            type = #primitive_type{name = 'Int', location = Location},
            location = Location
        }
    ],

    RecordDef1 = #record_def{
        name = 'Simple',
        fields = Fields1,
        location = Location
    },

    {ok, #instance_def{constraints = Constraints1}} =
        cure_derive:derive_instance('Show', RecordDef1, [], undefined),

    % Should have no constraints for non-parameterized types
    case Constraints1 of
        [] -> ok;
        _ -> throw({unexpected_constraints, Constraints1})
    end.

test_field_constraints_parameterized() ->
    Location = #location{line = 1, column = 1, file = "test.cure"},

    % Record with type variable field - should generate constraint
    Fields = [
        #record_field_def{
            name = value,
            % Type variable
            type = #primitive_type{name = 'T', location = Location},
            location = Location
        }
    ],

    RecordDef = #record_def{
        name = 'Container',
        fields = Fields,
        location = Location
    },

    {ok, #instance_def{constraints = Constraints}} =
        cure_derive:derive_instance('Show', RecordDef, [], undefined),

    % Should have Show(T) constraint
    case
        lists:any(
            fun(#typeclass_constraint{typeclass = TC, type_args = [#primitive_type{name = N}]}) ->
                TC =:= 'Show' andalso N =:= 'T'
            end,
            Constraints
        )
    of
        true -> ok;
        false -> throw(missing_show_t_constraint)
    end.
