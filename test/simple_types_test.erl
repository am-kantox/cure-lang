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
    cure_utils:debug("Running simple type system test...~n"),

    % Test builtin_env
    Env = cure_typechecker:builtin_env(),
    cure_utils:debug("✓ Builtin env created: ~p~n", [element(1, Env)]),

    % Test basic literal type inference
    IntLiteral = #literal_expr{
        type = 42, location = #location{line = 1, column = 1, file = undefined}
    },

    try
        Result = cure_typechecker:check_expression(IntLiteral, Env),
        cure_utils:debug("✓ Expression check result: ~p~n", [Result]),
        case Result of
            #typecheck_result{success = true, type = Type} ->
                cure_utils:debug("✓ Type inferred: ~p~n", [Type]);
            #typecheck_result{success = false, errors = Errors} ->
                cure_utils:debug("✗ Type checking failed with errors: ~p~n", [Errors])
        end
    catch
        Error:Reason:Stack ->
            cure_utils:debug("✗ Exception occurred: ~p:~p~n", [Error, Reason]),
            cure_utils:debug("Stack: ~p~n", [Stack])
    end,

    cure_utils:debug("Simple test completed!~n").
