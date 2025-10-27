-module(fsm_guard_verification_demo).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").

% Define records locally since they're not exported from typechecker
-record(typecheck_result, {
    success :: boolean(),
    type :: term() | undefined,
    errors :: [term()],
    warnings :: [term()]
}).
-record(typecheck_error, {message :: string(), location :: term(), details :: term()}).
-record(typecheck_warning, {message :: string(), location :: term(), details :: term()}).

run() ->
    io:format("~n=== FSM Guard Verification Demo ===~n~n"),

    % Create a simple FSM with guards
    Location = #location{line = 1, column = 1, file = <<"test.cure">>},

    % State: idle, active
    States = [idle, active],
    Initial = idle,

    % Transition with guard: idle --[start when x > 0]--> active
    GuardExpr = #binary_op_expr{
        op = '>',
        left = #identifier_expr{name = x, location = Location},
        right = #literal_expr{value = 0, location = Location},
        location = Location
    },

    Transition1 = #transition{
        event = #identifier_expr{name = start, location = Location},
        guard = GuardExpr,
        target = active,
        action = undefined,
        timeout = undefined,
        location = Location
    },

    % Transition without guard: active --[stop]--> idle
    Transition2 = #transition{
        event = #identifier_expr{name = stop, location = Location},
        guard = undefined,
        target = idle,
        action = undefined,
        timeout = undefined,
        location = Location
    },

    StateDef1 = #state_def{
        name = idle,
        transitions = [Transition1],
        location = Location
    },

    StateDef2 = #state_def{
        name = active,
        transitions = [Transition2],
        location = Location
    },

    FSM = #fsm_def{
        name = 'DemoFSM',
        states = States,
        initial = Initial,
        state_defs = [StateDef1, StateDef2],
        location = Location
    },

    % Type check the FSM
    Env = cure_typechecker:builtin_env(),
    io:format("Checking FSM with guard verification...~n"),

    case cure_typechecker:check_fsm(FSM, Env) of
        {ok, _NewEnv, Result} ->
            case Result#typecheck_result.success of
                true ->
                    io:format("✓ FSM type checking PASSED~n"),
                    io:format("  - Guards verified successfully~n"),
                    io:format("  - Warnings: ~p~n", [length(Result#typecheck_result.warnings)]),
                    case Result#typecheck_result.warnings of
                        [] ->
                            io:format("  - No warnings~n");
                        Warnings ->
                            lists:foreach(
                                fun(W) ->
                                    io:format("    Warning: ~s~n", [W#typecheck_warning.message])
                                end,
                                Warnings
                            )
                    end;
                false ->
                    io:format("✗ FSM type checking FAILED~n"),
                    lists:foreach(
                        fun(E) ->
                            io:format("  Error: ~s~n", [E#typecheck_error.message])
                        end,
                        Result#typecheck_result.errors
                    )
            end;
        {error, Error} ->
            io:format("✗ Error checking FSM: ~p~n", [Error])
    end,

    io:format("~n=== Demo Complete ===~n"),
    ok.
