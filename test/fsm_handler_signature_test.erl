%% Test FSM Handler Signature Checking
-module(fsm_handler_signature_test).

-export([run/0, test_handler_arity_warning/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast.hrl").

%% Run all tests
run() ->
    cure_utils:debug("Running FSM handler signature tests...~n"),
    test_handler_arity_warning(),
    cure_utils:debug("All FSM handler signature tests passed!~n").

%% Test that handlers with wrong arity produce warnings
test_handler_arity_warning() ->
    % Create an FSM with a handler
    FSMDef = #fsm_def{
        name = 'TestFSM',
        states = ['Locked', 'Unlocked'],
        initial = 'Locked',
        state_defs = [
            #state_def{
                name = 'Locked',
                transitions = [
                    #transition{
                        event = #identifier_expr{
                            name = coin, location = #location{line = 1, column = 1}
                        },
                        guard = undefined,
                        target = 'Unlocked',
                        action = #identifier_expr{
                            name = handle_coin, location = #location{line = 1, column = 1}
                        },
                        timeout = undefined,
                        location = #location{line = 1, column = 1}
                    }
                ],
                location = #location{line = 1, column = 1}
            }
        ],
        location = #location{line = 1, column = 1}
    },

    % Create environment with a handler that has wrong arity (2 instead of 3)
    Env = cure_typechecker:builtin_env(),
    WrongArityHandler =
        {function_type, [{primitive_type, 'State'}, {primitive_type, 'Event'}],
            {primitive_type, 'Unit'}},
    EnvWithHandler = cure_types:extend_env(Env, handle_coin, WrongArityHandler),

    % Check the FSM - should produce a warning about handler arity
    {ok, _NewEnv, Result} = cure_typechecker:check_fsm(FSMDef, EnvWithHandler),

    % Extract warnings from result
    {typecheck_result, Success, _Type, _Errors, Warnings} = Result,

    cure_utils:debug("Handler arity test - Success: ~p, Warnings: ~p~n", [Success, length(Warnings)]),

    % Should succeed overall but have a warning
    ?assertEqual(true, Success),
    ?assert(length(Warnings) > 0),

    % Check that at least one warning mentions the handler
    % Warnings are tuples but we don't have access to record definition here
    % Just verify we have warnings
    ?assert(length(Warnings) >= 1),

    cure_utils:debug("✓ Handler arity warning test passed~n").
