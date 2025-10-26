%% Comprehensive FSM Type Checking Tests
-module(fsm_comprehensive_test).

-export([
    run/0,
    test_unreachable_states/0,
    test_nondeterministic_fsm/0,
    test_handler_signature_warning/0,
    test_terminal_state_fsm/0,
    test_complex_fsm/0
]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast.hrl").

%% Run all tests
run() ->
    io:format("Running comprehensive FSM type checking tests...~n"),
    test_unreachable_states(),
    test_nondeterministic_fsm(),
    test_handler_signature_warning(),
    test_terminal_state_fsm(),
    test_complex_fsm(),
    io:format("All comprehensive FSM tests passed!~n").

%% Test FSM with unreachable states
test_unreachable_states() ->
    FSMDef = #fsm_def{
        name = 'UnreachableFSM',
        states = ['Start', 'Middle', 'End', 'Unreachable'],
        initial = 'Start',
        state_defs = [
            #state_def{
                name = 'Start',
                transitions = [
                    #transition{
                        event = #identifier_expr{
                            name = next, location = #location{line = 1, column = 1}
                        },
                        guard = undefined,
                        target = 'Middle',
                        action = undefined,
                        timeout = undefined,
                        location = #location{line = 1, column = 1}
                    }
                ],
                location = #location{line = 1, column = 1}
            },
            #state_def{
                name = 'Middle',
                transitions = [
                    #transition{
                        event = #identifier_expr{
                            name = finish, location = #location{line = 1, column = 1}
                        },
                        guard = undefined,
                        target = 'End',
                        action = undefined,
                        timeout = undefined,
                        location = #location{line = 1, column = 1}
                    }
                ],
                location = #location{line = 1, column = 1}
            },
            #state_def{
                name = 'Unreachable',
                transitions = [],
                location = #location{line = 1, column = 1}
            }
        ],
        location = #location{line = 1, column = 1}
    },

    Env = cure_typechecker:builtin_env(),
    {ok, _NewEnv, Result} = cure_typechecker:check_fsm(FSMDef, Env),
    {typecheck_result, Success, _Type, _Errors, Warnings} = Result,

    % Should succeed but have warnings about unreachable state
    ?assertEqual(true, Success),
    ?assert(length(Warnings) > 0),

    io:format("✓ Unreachable states test passed~n").

%% Test non-deterministic FSM (multiple transitions on same event)
test_nondeterministic_fsm() ->
    FSMDef = #fsm_def{
        name = 'NondeterministicFSM',
        states = ['Start', 'Path1', 'Path2'],
        initial = 'Start',
        state_defs = [
            #state_def{
                name = 'Start',
                transitions = [
                    #transition{
                        event = #identifier_expr{
                            name = choice, location = #location{line = 1, column = 1}
                        },
                        guard = undefined,
                        target = 'Path1',
                        action = undefined,
                        timeout = undefined,
                        location = #location{line = 1, column = 1}
                    },
                    #transition{
                        event = #identifier_expr{
                            name = choice, location = #location{line = 1, column = 1}
                        },
                        guard = undefined,
                        target = 'Path2',
                        action = undefined,
                        timeout = undefined,
                        location = #location{line = 1, column = 1}
                    }
                ],
                location = #location{line = 1, column = 1}
            }
        ],
        location = #location{line = 1, column = 1}
    },

    Env = cure_typechecker:builtin_env(),
    {ok, _NewEnv, Result} = cure_typechecker:check_fsm(FSMDef, Env),
    {typecheck_result, Success, _Type, _Errors, _Warnings} = Result,

    % Should succeed - non-determinism is allowed
    ?assertEqual(true, Success),

    io:format("✓ Non-deterministic FSM test passed~n").

%% Test handler signature warning
test_handler_signature_warning() ->
    FSMDef = #fsm_def{
        name = 'HandlerFSM',
        states = ['Active', 'Inactive'],
        initial = 'Active',
        state_defs = [
            #state_def{
                name = 'Active',
                transitions = [
                    #transition{
                        event = #identifier_expr{
                            name = deactivate, location = #location{line = 1, column = 1}
                        },
                        guard = undefined,
                        target = 'Inactive',
                        action = #identifier_expr{
                            name = wrong_handler, location = #location{line = 1, column = 1}
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

    % Create handler with wrong arity
    Env = cure_typechecker:builtin_env(),
    WrongHandler = {function_type, [{primitive_type, 'Event'}], {primitive_type, 'Unit'}},
    EnvWithHandler = cure_types:extend_env(Env, wrong_handler, WrongHandler),

    {ok, _NewEnv, Result} = cure_typechecker:check_fsm(FSMDef, EnvWithHandler),
    {typecheck_result, Success, _Type, _Errors, Warnings} = Result,

    % Should succeed but have warning
    ?assertEqual(true, Success),
    ?assert(length(Warnings) > 0),

    io:format("✓ Handler signature warning test passed~n").

%% Test FSM with terminal state (no outgoing transitions)
test_terminal_state_fsm() ->
    FSMDef = #fsm_def{
        name = 'TerminalFSM',
        states = ['Start', 'Processing', 'Done'],
        initial = 'Start',
        state_defs = [
            #state_def{
                name = 'Start',
                transitions = [
                    #transition{
                        event = #identifier_expr{
                            name = begin_process, location = #location{line = 1, column = 1}
                        },
                        guard = undefined,
                        target = 'Processing',
                        action = undefined,
                        timeout = undefined,
                        location = #location{line = 1, column = 1}
                    }
                ],
                location = #location{line = 1, column = 1}
            },
            #state_def{
                name = 'Processing',
                transitions = [
                    #transition{
                        event = #identifier_expr{
                            name = complete, location = #location{line = 1, column = 1}
                        },
                        guard = undefined,
                        target = 'Done',
                        action = undefined,
                        timeout = undefined,
                        location = #location{line = 1, column = 1}
                    }
                ],
                location = #location{line = 1, column = 1}
            },
            #state_def{
                name = 'Done',
                % Terminal state
                transitions = [],
                location = #location{line = 1, column = 1}
            }
        ],
        location = #location{line = 1, column = 1}
    },

    Env = cure_typechecker:builtin_env(),
    {ok, _NewEnv, Result} = cure_typechecker:check_fsm(FSMDef, Env),
    {typecheck_result, Success, _Type, _Errors, _Warnings} = Result,

    % Should succeed
    ?assertEqual(true, Success),

    io:format("✓ Terminal state FSM test passed~n").

%% Test complex FSM with multiple paths
test_complex_fsm() ->
    FSMDef = #fsm_def{
        name = 'ComplexFSM',
        states = ['Idle', 'Running', 'Paused', 'Error', 'Completed'],
        initial = 'Idle',
        state_defs = [
            #state_def{
                name = 'Idle',
                transitions = [
                    #transition{
                        event = #identifier_expr{
                            name = start, location = #location{line = 1, column = 1}
                        },
                        guard = undefined,
                        target = 'Running',
                        action = undefined,
                        timeout = undefined,
                        location = #location{line = 1, column = 1}
                    }
                ],
                location = #location{line = 1, column = 1}
            },
            #state_def{
                name = 'Running',
                transitions = [
                    #transition{
                        event = #identifier_expr{
                            name = pause, location = #location{line = 1, column = 1}
                        },
                        guard = undefined,
                        target = 'Paused',
                        action = undefined,
                        timeout = undefined,
                        location = #location{line = 1, column = 1}
                    },
                    #transition{
                        event = #identifier_expr{
                            name = error, location = #location{line = 1, column = 1}
                        },
                        guard = undefined,
                        target = 'Error',
                        action = undefined,
                        timeout = undefined,
                        location = #location{line = 1, column = 1}
                    },
                    #transition{
                        event = #identifier_expr{
                            name = complete, location = #location{line = 1, column = 1}
                        },
                        guard = undefined,
                        target = 'Completed',
                        action = undefined,
                        timeout = undefined,
                        location = #location{line = 1, column = 1}
                    }
                ],
                location = #location{line = 1, column = 1}
            },
            #state_def{
                name = 'Paused',
                transitions = [
                    #transition{
                        event = #identifier_expr{
                            name = resume, location = #location{line = 1, column = 1}
                        },
                        guard = undefined,
                        target = 'Running',
                        action = undefined,
                        timeout = undefined,
                        location = #location{line = 1, column = 1}
                    },
                    #transition{
                        event = #identifier_expr{
                            name = cancel, location = #location{line = 1, column = 1}
                        },
                        guard = undefined,
                        target = 'Idle',
                        action = undefined,
                        timeout = undefined,
                        location = #location{line = 1, column = 1}
                    }
                ],
                location = #location{line = 1, column = 1}
            },
            #state_def{
                name = 'Error',
                transitions = [
                    #transition{
                        event = #identifier_expr{
                            name = reset, location = #location{line = 1, column = 1}
                        },
                        guard = undefined,
                        target = 'Idle',
                        action = undefined,
                        timeout = undefined,
                        location = #location{line = 1, column = 1}
                    }
                ],
                location = #location{line = 1, column = 1}
            },
            #state_def{
                name = 'Completed',
                % Terminal state
                transitions = [],
                location = #location{line = 1, column = 1}
            }
        ],
        location = #location{line = 1, column = 1}
    },

    Env = cure_typechecker:builtin_env(),
    {ok, _NewEnv, Result} = cure_typechecker:check_fsm(FSMDef, Env),
    {typecheck_result, Success, _Type, _Errors, _Warnings} = Result,

    % Should succeed
    ?assertEqual(true, Success),

    io:format("✓ Complex FSM test passed~n").
