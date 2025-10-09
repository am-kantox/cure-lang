%% Simplified Type System Tests - Compatible with actual typechecker
-module(types_simple_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast_simple.hrl").

%% Type checking result record (from cure_typechecker.erl)
-record(typecheck_result, {
    success :: boolean(),
    type :: term() | undefined,
    errors :: [term()],
    warnings :: [term()]
}).

%% Run all simplified type system tests
run() ->
    io:format("Running Type System Simple tests...~n"),
    test_basic_type_inference(),
    test_simple_function_checking(),
    test_list_type_inference(),
    test_basic_unification(),
    io:format("All type system simple tests passed!~n").

%% Test basic type inference
test_basic_type_inference() ->
    % Test literal type inference
    Env = cure_typechecker:builtin_env(),

    % Integer literal
    IntLiteral = #literal_expr{value = 42, location = create_location(1, 1)},
    Result1 = cure_typechecker:check_expression(IntLiteral, Env),
    ?assertMatch(#typecheck_result{success = true}, Result1),
    ?assertMatch({primitive_type, 'Int'}, Result1#typecheck_result.type),

    % String literal
    StringLiteral = #literal_expr{value = "hello", location = create_location(1, 1)},
    Result2 = cure_typechecker:check_expression(StringLiteral, Env),
    ?assertMatch(#typecheck_result{success = true}, Result2),
    ?assertMatch({primitive_type, 'String'}, Result2#typecheck_result.type),

    % Boolean literal
    BoolLiteral = #literal_expr{value = true, location = create_location(1, 1)},
    Result3 = cure_typechecker:check_expression(BoolLiteral, Env),
    ?assertMatch(#typecheck_result{success = true}, Result3),
    ?assertMatch({primitive_type, 'Bool'}, Result3#typecheck_result.type),

    io:format("✓ Basic type inference test passed~n").

%% Test simple function type checking
test_simple_function_checking() ->
    % Test simple function: def add(x: Int, y: Int): Int = x + y
    Function = #function_def{
        name = add,
        params = [
            #param{
                name = x, type = #primitive_type{name = 'Int'}, location = create_location(1, 1)
            },
            #param{name = y, type = #primitive_type{name = 'Int'}, location = create_location(1, 1)}
        ],
        return_type = #primitive_type{name = 'Int'},
        constraint = undefined,
        body = #binary_op_expr{
            op = '+',
            left = #identifier_expr{name = x, location = create_location(1, 1)},
            right = #identifier_expr{name = y, location = create_location(1, 1)},
            location = create_location(1, 1)
        },
        location = create_location(1, 1)
    },

    Result = cure_typechecker:check_function(Function),
    ?assertMatch({ok, _Env, #typecheck_result{success = true}}, Result),

    io:format("✓ Simple function checking test passed~n").

%% Test list type inference
test_list_type_inference() ->
    Env = cure_typechecker:builtin_env(),

    % Test list literal [1, 2, 3]
    ListExpr = #list_expr{
        elements = [
            #literal_expr{value = 1, location = create_location(1, 1)},
            #literal_expr{value = 2, location = create_location(1, 1)},
            #literal_expr{value = 3, location = create_location(1, 1)}
        ],
        location = create_location(1, 1)
    },

    Result = cure_typechecker:check_expression(ListExpr, Env),
    ?assertMatch(#typecheck_result{success = true}, Result),
    ?assertMatch({list_type, {primitive_type, 'Int'}, _}, Result#typecheck_result.type),

    io:format("✓ List type inference test passed~n").

%% Test basic type unification
test_basic_unification() ->
    % Test basic unification
    Type1 = {primitive_type, 'Int'},
    Type2 = {primitive_type, 'Int'},
    Result1 = cure_types:unify(Type1, Type2),
    ?assertMatch({ok, _}, Result1),

    % Test unification failure
    Type3 = {primitive_type, 'String'},
    Result2 = cure_types:unify(Type1, Type3),
    ?assertMatch({error, _}, Result2),

    % Test type variable unification
    TypeVar = cure_types:new_type_var(),
    Result3 = cure_types:unify(TypeVar, Type1),
    ?assertMatch({ok, _}, Result3),

    io:format("✓ Basic unification test passed~n").

%% Helper functions
create_location(Line, Column) ->
    #location{line = Line, column = Column, file = "test"}.
