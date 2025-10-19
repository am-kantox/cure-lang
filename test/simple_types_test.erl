%% Simple Type System Test for Debugging
-module(simple_types_test).

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

%% Run a simple test
run() ->
    io:format("Running simple type system test...~n"),

    % Test builtin_env
    Env = cure_typechecker:builtin_env(),
    io:format("✓ Builtin env created: ~p~n", [element(1, Env)]),

    % Test basic literal type inference
    IntLiteral = #literal_expr{
        value = 42, location = #location{line = 1, column = 1, file = undefined}
    },

    try
        Result = cure_typechecker:check_expression(IntLiteral, Env),
        io:format("✓ Expression check result: ~p~n", [Result]),
        case Result of
            #typecheck_result{success = true, type = Type} ->
                io:format("✓ Type inferred: ~p~n", [Type]);
            #typecheck_result{success = false, errors = Errors} ->
                io:format("✗ Type checking failed with errors: ~p~n", [Errors])
        end
    catch
        Error:Reason:Stack ->
            io:format("✗ Exception occurred: ~p:~p~n", [Error, Reason]),
            io:format("Stack: ~p~n", [Stack])
    end,

    io:format("Simple test completed!~n").
