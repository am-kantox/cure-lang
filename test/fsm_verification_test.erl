-module(fsm_verification_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").

%% Test FSM verification
run() ->
    io:format("Running FSM Verification Tests...~n", []),
    Results = [
        test_no_deadlocks(),
        test_detect_deadlock(),
        test_reachability_simple(),
        test_unreachable_state(),
        test_liveness_satisfied(),
        test_liveness_violated(),
        test_safety_satisfied(),
        test_safety_violated()
    ],
    Passed = length([R || R <- Results, R =:= pass]),
    Failed = length([R || R <- Results, R =:= fail]),
    io:format("~n=== FSM Verification Test Results ===~n", []),
    io:format("Passed: ~p~n", [Passed]),
    io:format("Failed: ~p~n", [Failed]),
    if
        Failed =:= 0 ->
            io:format("All tests passed!~n", []),
            ok;
        true ->
            io:format("Some tests failed.~n", []),
            {error, {failed, Failed}}
    end.

%% ============================================================================
%% Deadlock Detection Tests
%% ============================================================================

test_no_deadlocks() ->
    io:format("Test: FSM with no deadlocks...~n", []),

    % Simple traffic light: Green -> Yellow -> Red -> Green
    FsmDef = #fsm_def{
        name = traffic_light,
        states = [green, yellow, red],
        initial = green,
        state_defs = [
            #state_def{
                name = green,
                transitions = [
                    #transition{
                        event = timer,
                        guard = undefined,
                        target = yellow,
                        action = undefined,
                        timeout = undefined,
                        location = loc()
                    }
                ],
                location = loc()
            },
            #state_def{
                name = yellow,
                transitions = [
                    #transition{
                        event = timer,
                        guard = undefined,
                        target = red,
                        action = undefined,
                        timeout = undefined,
                        location = loc()
                    }
                ],
                location = loc()
            },
            #state_def{
                name = red,
                transitions = [
                    #transition{
                        event = timer,
                        guard = undefined,
                        target = green,
                        action = undefined,
                        timeout = undefined,
                        location = loc()
                    }
                ],
                location = loc()
            }
        ],
        location = loc()
    },

    try
        Results = cure_fsm_verifier:check_deadlocks(FsmDef),

        case Results of
            [] ->
                io:format("  ✓ No deadlocks detected (correct)~n", []),
                pass;
            Deadlocks ->
                io:format("  ✗ FAILED: Unexpected deadlocks: ~p~n", [Deadlocks]),
                fail
        end
    catch
        Error:Reason:_Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n", [Error, Reason]),
            fail
    end.

test_detect_deadlock() ->
    io:format("Test: FSM with deadlock state...~n", []),

    % FSM with terminal state (deadlock)
    FsmDef = #fsm_def{
        name = broken_fsm,
        states = [start, terminal],
        initial = start,
        state_defs = [
            #state_def{
                name = start,
                transitions = [
                    #transition{
                        event = go,
                        guard = undefined,
                        target = terminal,
                        action = undefined,
                        timeout = undefined,
                        location = loc()
                    }
                ],
                location = loc()
            },
            #state_def{
                name = terminal,
                % No outgoing transitions - deadlock!
                transitions = [],
                location = loc()
            }
        ],
        location = loc()
    },

    try
        Results = cure_fsm_verifier:check_deadlocks(FsmDef),

        HasDeadlock = lists:any(
            fun
                ({has_deadlock, State}) when State =:= terminal -> true;
                (_) -> false
            end,
            Results
        ),

        if
            HasDeadlock ->
                io:format("  ✓ Correctly detected deadlock in terminal state~n", []),
                pass;
            true ->
                io:format("  ✗ FAILED: Did not detect expected deadlock~n", []),
                fail
        end
    catch
        Error:Reason:_Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n", [Error, Reason]),
            fail
    end.

%% ============================================================================
%% Reachability Tests
%% ============================================================================

test_reachability_simple() ->
    io:format("Test: Reachability in simple FSM...~n", []),

    % Linear FSM: A -> B -> C
    FsmDef = #fsm_def{
        name = linear_fsm,
        states = [a, b, c],
        initial = a,
        state_defs = [
            #state_def{
                name = a,
                transitions = [
                    #transition{
                        event = next,
                        guard = undefined,
                        target = b,
                        action = undefined,
                        timeout = undefined,
                        location = loc()
                    }
                ],
                location = loc()
            },
            #state_def{
                name = b,
                transitions = [
                    #transition{
                        event = next,
                        guard = undefined,
                        target = c,
                        action = undefined,
                        timeout = undefined,
                        location = loc()
                    }
                ],
                location = loc()
            },
            #state_def{
                name = c,
                transitions = [
                    #transition{
                        event = restart,
                        guard = undefined,
                        target = a,
                        action = undefined,
                        timeout = undefined,
                        location = loc()
                    }
                ],
                location = loc()
            }
        ],
        location = loc()
    },

    try
        % Check that C is reachable from A
        Result = cure_fsm_verifier:check_reachability(FsmDef, a, c),

        case Result of
            {reachable, c} ->
                io:format("  ✓ State C correctly identified as reachable from A~n", []),
                pass;
            Other ->
                io:format("  ✗ FAILED: Unexpected result: ~p~n", [Other]),
                fail
        end
    catch
        Error:Reason:_Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n", [Error, Reason]),
            fail
    end.

test_unreachable_state() ->
    io:format("Test: Detect unreachable state...~n", []),

    % FSM with unreachable state: A -> B, but C is isolated
    FsmDef = #fsm_def{
        name = disconnected_fsm,
        states = [a, b, c],
        initial = a,
        state_defs = [
            #state_def{
                name = a,
                transitions = [
                    #transition{
                        event = go,
                        guard = undefined,
                        target = b,
                        action = undefined,
                        timeout = undefined,
                        location = loc()
                    }
                ],
                location = loc()
            },
            #state_def{
                name = b,
                transitions = [
                    #transition{
                        event = back,
                        guard = undefined,
                        target = a,
                        action = undefined,
                        timeout = undefined,
                        location = loc()
                    }
                ],
                location = loc()
            },
            #state_def{
                % Isolated - no incoming transitions
                name = c,
                transitions = [],
                location = loc()
            }
        ],
        location = loc()
    },

    try
        Result = cure_fsm_verifier:check_reachability(FsmDef, a, c),

        case Result of
            {unreachable, c} ->
                io:format("  ✓ State C correctly identified as unreachable~n", []),
                pass;
            Other ->
                io:format("  ✗ FAILED: Expected unreachable, got: ~p~n", [Other]),
                fail
        end
    catch
        Error:Reason:_Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n", [Error, Reason]),
            fail
    end.

%% ============================================================================
%% Liveness Tests
%% ============================================================================

test_liveness_satisfied() ->
    io:format("Test: Liveness satisfied (no terminal states)...~n", []),

    % Cyclic FSM - always can make progress
    FsmDef = #fsm_def{
        name = cyclic_fsm,
        states = [s1, s2],
        initial = s1,
        state_defs = [
            #state_def{
                name = s1,
                transitions = [
                    #transition{
                        event = flip,
                        guard = undefined,
                        target = s2,
                        action = undefined,
                        timeout = undefined,
                        location = loc()
                    }
                ],
                location = loc()
            },
            #state_def{
                name = s2,
                transitions = [
                    #transition{
                        event = flip,
                        guard = undefined,
                        target = s1,
                        action = undefined,
                        timeout = undefined,
                        location = loc()
                    }
                ],
                location = loc()
            }
        ],
        location = loc()
    },

    try
        Results = cure_fsm_verifier:check_liveness(FsmDef),

        HasLiveness = lists:member({liveness_satisfied}, Results),

        if
            HasLiveness ->
                io:format("  ✓ Liveness property satisfied~n", []),
                pass;
            true ->
                io:format("  ✗ FAILED: Liveness not satisfied: ~p~n", [Results]),
                fail
        end
    catch
        Error:Reason:_Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n", [Error, Reason]),
            fail
    end.

test_liveness_violated() ->
    io:format("Test: Liveness violated (has terminal state)...~n", []),

    % FSM with terminal state violates liveness
    FsmDef = #fsm_def{
        name = terminal_fsm,
        states = [active, done],
        initial = active,
        state_defs = [
            #state_def{
                name = active,
                transitions = [
                    #transition{
                        event = finish,
                        guard = undefined,
                        target = done,
                        action = undefined,
                        timeout = undefined,
                        location = loc()
                    }
                ],
                location = loc()
            },
            #state_def{
                name = done,
                % Terminal state
                transitions = [],
                location = loc()
            }
        ],
        location = loc()
    },

    try
        Results = cure_fsm_verifier:check_liveness(FsmDef),

        HasViolation = lists:any(
            fun
                ({liveness_violated, _}) -> true;
                (_) -> false
            end,
            Results
        ),

        if
            HasViolation ->
                io:format("  ✓ Liveness violation correctly detected~n", []),
                pass;
            true ->
                io:format("  ✗ FAILED: Expected liveness violation~n", []),
                fail
        end
    catch
        Error:Reason:_Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n", [Error, Reason]),
            fail
    end.

%% ============================================================================
%% Safety Tests
%% ============================================================================

test_safety_satisfied() ->
    io:format("Test: Safety property satisfied (bad state unreachable)...~n", []),

    % FSM where 'error' state is not reachable
    FsmDef = #fsm_def{
        name = safe_fsm,
        states = [ok, processing, error],
        initial = ok,
        state_defs = [
            #state_def{
                name = ok,
                transitions = [
                    #transition{
                        event = process,
                        guard = undefined,
                        target = processing,
                        action = undefined,
                        timeout = undefined,
                        location = loc()
                    }
                ],
                location = loc()
            },
            #state_def{
                name = processing,
                transitions = [
                    #transition{
                        event = done,
                        guard = undefined,
                        target = ok,
                        action = undefined,
                        timeout = undefined,
                        location = loc()
                    }
                ],
                location = loc()
            },
            #state_def{
                % Isolated error state - unreachable
                name = error,
                transitions = [],
                location = loc()
            }
        ],
        location = loc()
    },

    try
        Result = cure_fsm_verifier:check_safety(FsmDef, [error]),

        case Result of
            {safety_satisfied} ->
                io:format("  ✓ Safety property satisfied (error state unreachable)~n", []),
                pass;
            Other ->
                io:format("  ✗ FAILED: Expected safety satisfied, got: ~p~n", [Other]),
                fail
        end
    catch
        Error:Reason:_Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n", [Error, Reason]),
            fail
    end.

test_safety_violated() ->
    io:format("Test: Safety property violated (bad state reachable)...~n", []),

    % FSM where 'error' state is reachable
    FsmDef = #fsm_def{
        name = unsafe_fsm,
        states = [ok, error],
        initial = ok,
        state_defs = [
            #state_def{
                name = ok,
                transitions = [
                    #transition{
                        event = fail,
                        guard = undefined,
                        target = error,
                        action = undefined,
                        timeout = undefined,
                        location = loc()
                    }
                ],
                location = loc()
            },
            #state_def{
                name = error,
                transitions = [],
                location = loc()
            }
        ],
        location = loc()
    },

    try
        Result = cure_fsm_verifier:check_safety(FsmDef, [error]),

        case Result of
            {safety_violated, #{bad_state := error}} ->
                io:format("  ✓ Safety violation correctly detected~n", []),
                pass;
            Other ->
                io:format("  ✗ FAILED: Expected safety violation, got: ~p~n", [Other]),
                fail
        end
    catch
        Error:Reason:_Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n", [Error, Reason]),
            fail
    end.

%% ============================================================================
%% Helper Functions
%% ============================================================================

loc() ->
    #location{line = 0, column = 0, file = undefined}.
