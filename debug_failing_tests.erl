-module(debug_failing_tests).
-export([test/0]).

-include("src/parser/cure_ast_simple.hrl").

test() ->
    io:format("=== Debugging Failing Tests ===~n"),

    % Test 1: Vector unification
    io:format("~n1. Testing Vector(Float, 3) vs Vector(Float, 4) unification:~n"),
    Vec3 =
        {dependent_type, 'Vector', [
            #type_param{name = elem_type, value = {primitive_type, 'Float'}},
            #type_param{name = length, value = {literal_expr, 3, undefined}}
        ]},
    Vec4 =
        {dependent_type, 'Vector', [
            #type_param{name = elem_type, value = {primitive_type, 'Float'}},
            #type_param{name = length, value = {literal_expr, 4, undefined}}
        ]},

    case cure_types:unify(Vec3, Vec4) of
        {ok, _} -> io:format("  PROBLEM: Unification succeeded when it should fail~n");
        {error, Reason} -> io:format("  GOOD: Unification failed with reason: ~p~n", [Reason])
    end,

    % Test 2: Function type checking
    io:format("~n2. Testing function type with mismatched vector dimensions:~n"),
    InvalidFuncType = {function_type, [Vec3, Vec4], {primitive_type, 'Float'}},
    Env = cure_types:new_env(),

    case cure_types:check_type(undefined, InvalidFuncType, Env) of
        ok -> io:format("  PROBLEM: Type checking succeeded when it should fail~n");
        {error, Reason2} -> io:format("  GOOD: Type checking failed with reason: ~p~n", [Reason2])
    end,

    % Test 3: Occurs check
    io:format("~n3. Testing occurs check with recursive dependent type:~n"),
    TypeVar = cure_types:new_type_var(),
    io:format("  Created type variable: ~p~n", [TypeVar]),

    RecursiveType =
        {dependent_type, 'Vector', [
            #type_param{name = elem_type, value = TypeVar},
            #type_param{name = length, value = {literal_expr, 3, undefined}}
        ]},
    io:format("  Trying to unify with: ~p~n", [RecursiveType]),

    case cure_types:unify(TypeVar, RecursiveType) of
        {ok, _} ->
            io:format("  PROBLEM: Occurs check failed - infinite type allowed~n");
        {error, Reason3} ->
            io:format("  GOOD: Occurs check prevented infinite type: ~p~n", [Reason3])
    end,

    io:format("~n=== Debug Complete ===~n").
