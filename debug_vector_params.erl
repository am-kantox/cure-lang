-module(debug_vector_params).
-export([test/0]).

-include("src/parser/cure_ast_simple.hrl").

test() ->
    io:format("=== Debugging Vector Parameter Extraction ===~n"),

    Vec3 =
        {dependent_type, 'Vector', [
            #type_param{name = elem_type, value = {primitive_type, 'Float'}},
            #type_param{name = length, value = {literal_expr, 3, undefined}}
        ]},

    io:format("Vec3 structure: ~p~n", [Vec3]),

    case Vec3 of
        {dependent_type, 'Vector', Params} ->
            io:format("Matched Vector with params: ~p~n", [Params]),

            % Test extract_vector_params function
            case cure_types:unify(Vec3, Vec3) of
                {ok, Subst} ->
                    io:format("Vec3 unifies with itself: ~p~n", [Subst]);
                {error, Reason} ->
                    io:format("ERROR: Vec3 doesn't unify with itself: ~p~n", [Reason])
            end,

            % Test different lengths
            Vec4 =
                {dependent_type, 'Vector', [
                    #type_param{name = elem_type, value = {primitive_type, 'Float'}},
                    #type_param{name = length, value = {literal_expr, 4, undefined}}
                ]},

            case cure_types:unify(Vec3, Vec4) of
                {ok, Subst2} -> io:format("PROBLEM: Vec3 and Vec4 unify: ~p~n", [Subst2]);
                {error, Reason2} -> io:format("GOOD: Vec3 and Vec4 don't unify: ~p~n", [Reason2])
            end;
        _ ->
            io:format("Didn't match Vector pattern~n")
    end.
