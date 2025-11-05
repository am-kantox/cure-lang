-module(where_clause_test).

%% Test suite for where clause functionality
%% Tests parsing, validation, and constraint checking

-export([run/0]).

-include("../src/parser/cure_ast.hrl").

%% ============================================================================
%% Test Runner
%% ============================================================================

run() ->
    io:format("~n=== Where Clause Test Suite ===~n~n"),

    % Run all test categories
    Results = [
        {"Parsing Tests", run_parsing_tests()},
        {"Validation Tests", run_validation_tests()},
        {"Constraint Checking Tests", run_constraint_tests()}
    ],

    % Print summary
    print_summary(Results),

    % Return success if all passed
    AllPassed = lists:all(
        fun({_, {Pass, Fail}}) -> Fail == 0 andalso Pass > 0 end,
        Results
    ),
    case AllPassed of
        true -> ok;
        false -> {error, tests_failed}
    end.

%% ============================================================================
%% Parsing Tests
%% ============================================================================

run_parsing_tests() ->
    io:format("~n--- Parsing Tests ---~n"),

    Tests = [
        {"Parse function with single constraint", fun test_parse_single_constraint/0},
        {"Parse function with multiple constraints", fun test_parse_multiple_constraints/0},
        {"Parse function without where clause", fun test_parse_no_where/0},
        {"Parse where clause with Show(T)", fun test_parse_show_constraint/0},
        {"Parse where clause with Eq(T), Ord(T)", fun test_parse_multiple_typeclasses/0}
    ],

    run_tests(Tests).

test_parse_single_constraint() ->
    Code = <<"def print_list<T>(xs: List(T)) -> String where Show(T) = \"todo\"">>,
    case cure_lexer:tokenize(Code) of
        {ok, Tokens} ->
            Parser = cure_parser:new(Tokens),
            case cure_parser:parse_item(Parser) of
                {{ok, FuncDef}, _State} when is_record(FuncDef, function_def) ->
                    case FuncDef#function_def.where_clause of
                        #where_clause{constraints = [_Constraint]} ->
                            ok;
                        undefined ->
                            {error, where_clause_not_parsed};
                        Other ->
                            {error, {unexpected_where_clause, Other}}
                    end;
                {error, Reason} ->
                    {error, {parse_error, Reason}};
                Other ->
                    {error, {unexpected_result, Other}}
            end;
        {error, Reason} ->
            {error, {lex_error, Reason}}
    end.

test_parse_multiple_constraints() ->
    Code =
        <<"def compare_list<T>(xs: List(T), ys: List(T)) -> Bool where Eq(T), Ord(T) = \"todo\"">>,
    case cure_lexer:tokenize(Code) of
        {ok, Tokens} ->
            Parser = cure_parser:new(Tokens),
            case cure_parser:parse_item(Parser) of
                {{ok, FuncDef}, _State} when is_record(FuncDef, function_def) ->
                    case FuncDef#function_def.where_clause of
                        #where_clause{constraints = [_, _]} ->
                            ok;
                        undefined ->
                            {error, where_clause_not_parsed};
                        Other ->
                            {error, {unexpected_where_clause, Other}}
                    end;
                {error, Reason} ->
                    {error, {parse_error, Reason}};
                Other ->
                    {error, {unexpected_result, Other}}
            end;
        {error, Reason} ->
            {error, {lex_error, Reason}}
    end.

test_parse_no_where() ->
    Code = <<"def simple(x: Int) -> Int = x">>,
    case cure_lexer:tokenize(Code) of
        {ok, Tokens} ->
            Parser = cure_parser:new(Tokens),
            case cure_parser:parse_item(Parser) of
                {{ok, FuncDef}, _State} when is_record(FuncDef, function_def) ->
                    case FuncDef#function_def.where_clause of
                        undefined ->
                            ok;
                        Other ->
                            {error, {unexpected_where_clause, Other}}
                    end;
                {error, Reason} ->
                    {error, {parse_error, Reason}};
                Other ->
                    {error, {unexpected_result, Other}}
            end;
        {error, Reason} ->
            {error, {lex_error, Reason}}
    end.

test_parse_show_constraint() ->
    Code = <<"def show_value<T>(x: T) -> String where Show(T) = \"todo\"">>,
    case cure_lexer:tokenize(Code) of
        {ok, Tokens} ->
            Parser = cure_parser:new(Tokens),
            case cure_parser:parse_item(Parser) of
                {{ok, FuncDef}, _State} when is_record(FuncDef, function_def) ->
                    case FuncDef#function_def.where_clause of
                        #where_clause{constraints = [Constraint]} ->
                            case Constraint of
                                #typeclass_constraint{typeclass = 'Show'} ->
                                    ok;
                                _ ->
                                    {error, {wrong_constraint, Constraint}}
                            end;
                        Other ->
                            {error, {unexpected_where_clause, Other}}
                    end;
                {error, Reason} ->
                    {error, {parse_error, Reason}};
                Other ->
                    {error, {unexpected_result, Other}}
            end;
        {error, Reason} ->
            {error, {lex_error, Reason}}
    end.

test_parse_multiple_typeclasses() ->
    Code = <<"def test<T>(x: T) -> Bool where Eq(T), Ord(T) = \"todo\"">>,
    case cure_lexer:tokenize(Code) of
        {ok, Tokens} ->
            Parser = cure_parser:new(Tokens),
            case cure_parser:parse_item(Parser) of
                {{ok, FuncDef}, _State} when is_record(FuncDef, function_def) ->
                    case FuncDef#function_def.where_clause of
                        #where_clause{constraints = [C1, C2]} ->
                            TC1 = C1#typeclass_constraint.typeclass,
                            TC2 = C2#typeclass_constraint.typeclass,
                            case {TC1, TC2} of
                                {'Eq', 'Ord'} -> ok;
                                _ -> {error, {wrong_typeclasses, TC1, TC2}}
                            end;
                        Other ->
                            {error, {unexpected_where_clause, Other}}
                    end;
                {error, Reason} ->
                    {error, {parse_error, Reason}};
                Other ->
                    {error, {unexpected_result, Other}}
            end;
        {error, Reason} ->
            {error, {lex_error, Reason}}
    end.

%% ============================================================================
%% Validation Tests
%% ============================================================================

run_validation_tests() ->
    io:format("~n--- Validation Tests ---~n"),

    Tests = [
        {"Validate undefined where clause", fun test_validate_undefined/0},
        {"Validate known typeclass", fun test_validate_known_typeclass/0},
        {"Reject unknown typeclass", fun test_reject_unknown_typeclass/0},
        {"Validate constraint arity", fun test_validate_arity/0},
        {"Reject duplicate constraints", fun test_reject_duplicates/0}
    ],

    run_tests(Tests).

test_validate_undefined() ->
    Env = cure_typeclass:new_env(),
    Result = cure_typeclass:validate_where_constraints(undefined, Env),
    assert_equals(ok, Result).

test_validate_known_typeclass() ->
    % Create environment with Show typeclass
    Env = create_test_env_with_show(),

    % Create where clause with Show(Int)
    IntType = #primitive_type{name = 'Int', location = undefined},
    Constraint = #typeclass_constraint{
        typeclass = 'Show',
        type_args = [IntType],
        location = undefined
    },
    WhereClause = #where_clause{
        constraints = [Constraint],
        location = undefined
    },

    Result = cure_typeclass:validate_where_constraints(WhereClause, Env),
    assert_equals(ok, Result).

test_reject_unknown_typeclass() ->
    Env = cure_typeclass:new_env(),

    % Create where clause with unknown typeclass
    IntType = #primitive_type{name = 'Int', location = undefined},
    Constraint = #typeclass_constraint{
        typeclass = 'UnknownClass',
        type_args = [IntType],
        location = undefined
    },
    WhereClause = #where_clause{
        constraints = [Constraint],
        location = undefined
    },

    case cure_typeclass:validate_where_constraints(WhereClause, Env) of
        {error, {unknown_typeclass, 'UnknownClass'}} -> ok;
        Other -> {error, {expected_unknown_typeclass_error, got, Other}}
    end.

test_validate_arity() ->
    % Create environment with Show typeclass (arity 1)
    Env = create_test_env_with_show(),

    % Create where clause with wrong arity (Show takes 1 arg, we give 2)
    IntType = #primitive_type{name = 'Int', location = undefined},
    Constraint = #typeclass_constraint{
        typeclass = 'Show',
        type_args = [IntType, IntType],
        location = undefined
    },
    WhereClause = #where_clause{
        constraints = [Constraint],
        location = undefined
    },

    case cure_typeclass:validate_where_constraints(WhereClause, Env) of
        {error, {arity_mismatch, 'Show', 1, 2}} -> ok;
        Other -> {error, {expected_arity_mismatch, got, Other}}
    end.

test_reject_duplicates() ->
    Env = create_test_env_with_show(),

    % Create where clause with duplicate constraints
    IntType = #primitive_type{name = 'Int', location = undefined},
    Constraint1 = #typeclass_constraint{
        typeclass = 'Show',
        type_args = [IntType],
        location = undefined
    },
    Constraint2 = #typeclass_constraint{
        typeclass = 'Show',
        type_args = [IntType],
        location = undefined
    },
    WhereClause = #where_clause{
        constraints = [Constraint1, Constraint2],
        location = undefined
    },

    case cure_typeclass:validate_where_constraints(WhereClause, Env) of
        {error, {duplicate_constraint, _}} -> ok;
        Other -> {error, {expected_duplicate_error, got, Other}}
    end.

%% Helper: Create test environment with Show typeclass
create_test_env_with_show() ->
    Env0 = cure_typeclass:new_env(),

    % Create Show typeclass definition
    ShowDef = #typeclass_def{
        name = 'Show',
        type_params = ['T'],
        constraints = [],
        methods = [
            #method_signature{
                name = show,
                type_params = [],
                params = [
                    #param{
                        name = x,
                        type = #primitive_type{name = 'T', location = undefined},
                        location = undefined
                    }
                ],
                return_type = #primitive_type{name = 'String', location = undefined},
                default_impl = undefined,
                location = undefined
            }
        ],
        default_methods = [],
        location = undefined
    },

    {ok, Env1} = cure_typeclass:register_typeclass(ShowDef, Env0),
    Env1.

%% ============================================================================
%% Constraint Checking Tests
%% ============================================================================

run_constraint_tests() ->
    io:format("~n--- Constraint Checking Tests ---~n"),

    Tests = [
        {"Check constraints are tracked", fun test_constraints_tracked/0},
        {"Multiple constraints validated", fun test_multiple_constraints/0}
    ],

    run_tests(Tests).

test_constraints_tracked() ->
    % This test verifies that where clause constraints are properly stored
    Code = <<"def helper<T>(x: T) -> String where Show(T) = \"result\"">>,
    case cure_lexer:tokenize(Code) of
        {ok, Tokens} ->
            Parser = cure_parser:new(Tokens),
            case cure_parser:parse_item(Parser) of
                {{ok, FuncDef}, _State} when is_record(FuncDef, function_def) ->
                    case FuncDef#function_def.where_clause of
                        #where_clause{constraints = Constraints} when length(Constraints) > 0 ->
                            ok;
                        _ ->
                            {error, constraints_not_tracked}
                    end;
                {error, Reason} ->
                    {error, {parse_error, Reason}};
                Other ->
                    {error, {unexpected_result, Other}}
            end;
        {error, Reason} ->
            {error, {lex_error, Reason}}
    end.

test_multiple_constraints() ->
    Env = create_test_env_with_multiple_typeclasses(),

    % Create where clause with multiple constraints
    TType = #primitive_type{name = 'T', location = undefined},
    Constraint1 = #typeclass_constraint{
        typeclass = 'Show',
        type_args = [TType],
        location = undefined
    },
    Constraint2 = #typeclass_constraint{
        typeclass = 'Eq',
        type_args = [TType],
        location = undefined
    },
    WhereClause = #where_clause{
        constraints = [Constraint1, Constraint2],
        location = undefined
    },

    Result = cure_typeclass:validate_where_constraints(WhereClause, Env),
    assert_equals(ok, Result).

%% Helper: Create test environment with multiple typeclasses
create_test_env_with_multiple_typeclasses() ->
    Env0 = cure_typeclass:new_env(),

    % Create Show typeclass
    ShowDef = #typeclass_def{
        name = 'Show',
        type_params = ['T'],
        constraints = [],
        methods = [
            #method_signature{
                name = show,
                type_params = [],
                params = [
                    #param{
                        name = x,
                        type = #primitive_type{name = 'T', location = undefined},
                        location = undefined
                    }
                ],
                return_type = #primitive_type{name = 'String', location = undefined},
                default_impl = undefined,
                location = undefined
            }
        ],
        default_methods = [],
        location = undefined
    },

    % Create Eq typeclass
    EqDef = #typeclass_def{
        name = 'Eq',
        type_params = ['T'],
        constraints = [],
        methods = [
            #method_signature{
                name = eq,
                type_params = [],
                params = [
                    #param{
                        name = x,
                        type = #primitive_type{name = 'T', location = undefined},
                        location = undefined
                    },
                    #param{
                        name = y,
                        type = #primitive_type{name = 'T', location = undefined},
                        location = undefined
                    }
                ],
                return_type = #primitive_type{name = 'Bool', location = undefined},
                default_impl = undefined,
                location = undefined
            }
        ],
        default_methods = [],
        location = undefined
    },

    {ok, Env1} = cure_typeclass:register_typeclass(ShowDef, Env0),
    {ok, Env2} = cure_typeclass:register_typeclass(EqDef, Env1),
    Env2.

%% ============================================================================
%% Test Helpers
%% ============================================================================

run_tests(Tests) ->
    Results = lists:map(
        fun({Name, TestFun}) ->
            io:format("  ~s: ", [Name]),
            try
                case TestFun() of
                    ok ->
                        io:format("PASS~n"),
                        {pass, Name};
                    {error, Reason} ->
                        io:format("FAIL: ~p~n", [Reason]),
                        {fail, Name, Reason}
                end
            catch
                Error:ReasonCaught:Stacktrace ->
                    io:format("ERROR: ~p:~p~n~p~n", [Error, ReasonCaught, Stacktrace]),
                    {fail, Name, {Error, ReasonCaught}}
            end
        end,
        Tests
    ),

    Passed = length([X || {pass, _} = X <- Results]),
    Failed = length([X || {fail, _, _} = X <- Results]),

    {Passed, Failed}.

assert_equals(Expected, Actual) ->
    case Expected =:= Actual of
        true -> ok;
        false -> {error, {expected, Expected, got, Actual}}
    end.

print_summary(Results) ->
    io:format("~n=== Test Summary ===~n"),

    TotalPass = lists:sum([Pass || {_, {Pass, _}} <- Results]),
    TotalFail = lists:sum([Fail || {_, {_, Fail}} <- Results]),
    Total = TotalPass + TotalFail,

    lists:foreach(
        fun({Category, {Pass, Fail}}) ->
            io:format("~s: ~p/~p passed~n", [Category, Pass, Pass + Fail])
        end,
        Results
    ),

    Percentage =
        if
            Total > 0 -> (TotalPass / Total) * 100;
            true -> 0.0
        end,

    io:format("~nTotal: ~p/~p passed (~.1f%)~n", [
        TotalPass,
        Total,
        Percentage
    ]),

    ok.
