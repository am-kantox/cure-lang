%% Type System Tests
-module(types_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast.hrl").

%% Type checking result record (from cure_typechecker.erl)
-record(typecheck_result, {
    success :: boolean(),
    type :: term() | undefined,
    errors :: [term()],
    warnings :: [term()]
}).

%% Run all type system tests
run() ->
    io:format("Running Type System tests...~n"),
    test_basic_type_inference(),
    test_function_type_checking(),
    test_list_type_inference(),
    test_dependent_types(),
    test_type_unification(),
    test_program_type_checking(),
    io:format("All type system tests passed!~n").

%% Test basic type inference
test_basic_type_inference() ->
    % Test literal type inference
    Env = cure_typechecker:builtin_env(),

    % Integer literal
    IntLiteral = #literal_expr{
        value = 42, location = #location{line = 1, column = 1, file = undefined}
    },
    Result1 = cure_typechecker:check_expression(IntLiteral, Env),
    ?assertMatch(#typecheck_result{success = true, type = {primitive_type, 'Int'}}, Result1),

    % String literal
    StringLiteral = #literal_expr{
        value = "hello", location = #location{line = 1, column = 1, file = undefined}
    },
    Result2 = cure_typechecker:check_expression(StringLiteral, Env),
    ?assertMatch(#typecheck_result{success = true, type = {primitive_type, 'String'}}, Result2),

    % Boolean literal
    BoolLiteral = #literal_expr{
        value = true, location = #location{line = 1, column = 1, file = undefined}
    },
    Result3 = cure_typechecker:check_expression(BoolLiteral, Env),
    ?assertMatch(#typecheck_result{success = true, type = {primitive_type, 'Bool'}}, Result3),

    io:format("✓ Basic type inference test passed~n").

%% Test function type checking
test_function_type_checking() ->
    % Test simple function: def add(x: Int, y: Int): Int = x + y
    Function = #function_def{
        name = add,
        params = [
            #param{
                name = x,
                type = #primitive_type{name = 'Int'},
                location = #location{line = 1, column = 1}
            },
            #param{
                name = y,
                type = #primitive_type{name = 'Int'},
                location = #location{line = 1, column = 1}
            }
        ],
        return_type = #primitive_type{name = 'Int'},
        constraint = undefined,
        body = #binary_op_expr{
            op = '+',
            left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
            right = #identifier_expr{name = y, location = #location{line = 1, column = 1}},
            location = #location{line = 1, column = 1}
        },
        location = #location{line = 1, column = 1}
    },

    Result = cure_typechecker:check_function(Function),
    ?assertMatch({ok, _Env, #typecheck_result{success = true}}, Result),

    io:format("✓ Function type checking test passed~n").

%% Test list type inference
test_list_type_inference() ->
    Env = cure_typechecker:builtin_env(),

    % Test list literal [1, 2, 3]
    ListExpr = #list_expr{
        elements = [
            #literal_expr{value = 1, location = #location{line = 1, column = 1}},
            #literal_expr{value = 2, location = #location{line = 1, column = 1}},
            #literal_expr{value = 3, location = #location{line = 1, column = 1}}
        ],
        location = #location{line = 1, column = 1}
    },

    Result = cure_typechecker:check_expression(ListExpr, Env),
    ?assertMatch(
        #typecheck_result{success = true, type = {list_type, {primitive_type, 'Int'}, _}}, Result
    ),

    io:format("✓ List type inference test passed~n").

%% Test dependent types
test_dependent_types() ->
    % Test that we can check constraints for dependent types
    % For now, just test that the type system handles dependent type annotations
    DependentType = #dependent_type{
        name = 'List',
        params = [#type_param{value = #primitive_type{name = 'Int'}}]
    },

    % Convert to tuple format and verify it's handled
    ConvertedType = cure_typechecker:convert_type_to_tuple(DependentType),
    ?assertMatch({dependent_type, 'List', _}, ConvertedType),

    io:format("✓ Dependent types test passed~n").

%% Test type unification
test_type_unification() ->
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

    io:format("✓ Type unification test passed~n").

%% Test program-level type checking
test_program_type_checking() ->
    % Create a simple program AST
    Program = [
        #function_def{
            name = double,
            params = [
                #param{
                    name = x,
                    type = #primitive_type{name = 'Int'},
                    location = #location{line = 1, column = 1}
                }
            ],
            return_type = #primitive_type{name = 'Int'},
            constraint = undefined,
            body = #binary_op_expr{
                op = '*',
                left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
                right = #literal_expr{value = 2, location = #location{line = 1, column = 1}},
                location = #location{line = 1, column = 1}
            },
            location = #location{line = 1, column = 1}
        }
    ],

    Result = cure_typechecker:check_program(Program),
    ?assertMatch(#typecheck_result{success = true}, Result),

    io:format("✓ Program type checking test passed~n").
