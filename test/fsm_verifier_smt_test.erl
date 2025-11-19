-module(fsm_verifier_smt_test).

-export([run/0]).

-include("../src/parser/cure_ast.hrl").

%% Test runner
run() ->
    io:format("~n=== FSM Verifier SMT Test Suite ===~n~n"),

    Tests = [
        {"Deadlock-free FSM (graph structure)", fun test_deadlock_free_graph/0},
        {"FSM with deadlock (graph structure)", fun test_with_deadlock_graph/0},
        {"Basic reachability (BFS)", fun test_basic_reachability/0},
        {"Unreachable state detection", fun test_unreachable_state/0},
        {"Liveness check (no deadlocks)", fun test_liveness_satisfied/0},
        {"Liveness violation (deadlocks present)", fun test_liveness_violated/0},
        {"Safety property (bad state unreachable)", fun test_safety_satisfied/0},
        {"Safety violation (bad state reachable)", fun test_safety_violated/0},
        {"SMT deadlock detection", fun test_smt_deadlock_detection/0},
        {"SMT reachability analysis", fun test_smt_reachability/0},
        {"SMT state invariant (always true)", fun test_smt_invariant_holds/0}
    ],

    Results = lists:map(
        fun({TestName, TestFun}) ->
            io:format("Running: ~s... ", [TestName]),
            try
                TestFun(),
                io:format("✓ PASS~n"),
                {pass, TestName}
            catch
                error:{assertion_failed, Reason} ->
                    io:format("✗ FAIL: ~p~n", [Reason]),
                    {fail, TestName, Reason};
                Class:Error:Stack ->
                    io:format("✗ ERROR: ~p:~p~n~p~n", [Class, Error, Stack]),
                    {error, TestName, {Class, Error}}
            end
        end,
        Tests
    ),

    Passed = length([R || {pass, _} = R <- Results]),
    Failed = length([R || {fail, _, _} = R <- Results]),
    Errors = length([R || {error, _, _} = R <- Results]),
    Total = length(Tests),

    io:format("~n=== Results ===~n"),
    io:format("Passed: ~p/~p~n", [Passed, Total]),
    io:format("Failed: ~p/~p~n", [Failed, Total]),
    io:format("Errors: ~p/~p~n", [Errors, Total]),

    if
        Passed =:= Total ->
            io:format("~n✓ All tests passed!~n"),
            halt(0);
        true ->
            io:format("~n✗ Some tests failed.~n"),
            halt(1)
    end.

%% ============================================================================
%% Test Cases
%% ============================================================================

test_deadlock_free_graph() ->
    % FSM with cycle: Ready -> Processing -> Ready
    Fsm = make_fsm(ready, [
        make_state(ready, [make_transition(start, processing)]),
        make_state(processing, [make_transition(complete, ready)])
    ]),

    Result = cure_fsm_verifier:check_deadlocks(Fsm),
    assert_equals([], Result, "Deadlock-free FSM should return empty list").

test_with_deadlock_graph() ->
    % FSM with deadlock: Ready -> Error (no outgoing transitions from Error)
    Fsm = make_fsm(ready, [
        make_state(ready, [make_transition(start, error)]),
        % Deadlock state
        make_state(error, [])
    ]),

    Result = cure_fsm_verifier:check_deadlocks(Fsm),
    assert_not_empty(Result, "FSM with deadlock should be detected").

test_basic_reachability() ->
    % FSM: A -> B -> C
    Fsm = make_fsm(a, [
        make_state(a, [make_transition(go, b)]),
        make_state(b, [make_transition(continue, c)]),
        make_state(c, [])
    ]),

    Result = cure_fsm_verifier:check_reachability(Fsm, a, c),
    assert_matches({reachable, c}, Result, "State C should be reachable from A").

test_unreachable_state() ->
    % FSM: A -> B, C is isolated
    Fsm = make_fsm(a, [
        make_state(a, [make_transition(go, b)]),
        make_state(b, []),
        % Unreachable
        make_state(c, [])
    ]),

    Result = cure_fsm_verifier:check_reachability(Fsm, a, c),
    assert_matches({unreachable, c}, Result, "State C should be unreachable").

test_liveness_satisfied() ->
    % FSM with all states having outgoing transitions
    Fsm = make_fsm(ready, [
        make_state(ready, [make_transition(start, processing)]),
        make_state(processing, [make_transition(complete, ready)])
    ]),

    Result = cure_fsm_verifier:check_liveness(Fsm),
    assert_contains({liveness_satisfied}, Result, "Liveness should be satisfied").

test_liveness_violated() ->
    % FSM with terminal state (violates liveness)
    Fsm = make_fsm(ready, [
        make_state(ready, [make_transition(start, terminal)]),
        % Terminal state
        make_state(terminal, [])
    ]),

    Result = cure_fsm_verifier:check_liveness(Fsm),
    case
        lists:any(
            fun
                ({liveness_violated, _}) -> true;
                (_) -> false
            end,
            Result
        )
    of
        true -> ok;
        false -> error({assertion_failed, {"Liveness should be violated", {result, Result}}})
    end.

test_safety_satisfied() ->
    % FSM where bad state 'error' is not reachable
    Fsm = make_fsm(ready, [
        make_state(ready, [make_transition(start, processing)]),
        make_state(processing, [make_transition(complete, ready)]),
        % Isolated bad state
        make_state(error, [])
    ]),

    Result = cure_fsm_verifier:check_safety(Fsm, [error]),
    assert_equals({safety_satisfied}, Result, "Safety should be satisfied").

test_safety_violated() ->
    % FSM where bad state 'error' is reachable
    Fsm = make_fsm(ready, [
        make_state(ready, [make_transition(start, error)]),
        make_state(error, [])
    ]),

    Result = cure_fsm_verifier:check_safety(Fsm, [error]),
    case Result of
        {safety_violated, _} -> ok;
        _ -> error({assertion_failed, {"Safety should be violated", {result, Result}}})
    end.

test_smt_deadlock_detection() ->
    % Test SMT-based deadlock detection
    Fsm = make_fsm(ready, [
        make_state(ready, [make_transition(start, processing)]),
        make_state(processing, [make_transition(complete, done)]),
        % Potential deadlock
        make_state(done, [])
    ]),

    Result = cure_fsm_verifier:check_deadlock_via_smt(Fsm),
    % Should detect that 'done' is a reachable deadlock state
    case Result of
        {ok, deadlock_free} ->
            error({assertion_failed, "Should detect deadlock"});
        {deadlock, done, _} ->
            % Expected: deadlock in 'done' state
            ok;
        {deadlock, _Other, _} ->
            % Some deadlock found
            ok;
        {error, Reason} ->
            % SMT might not be available - skip test
            io:format("Skipped (SMT error: ~p) ", [Reason]),
            ok
    end.

test_smt_reachability() ->
    % Test SMT-based reachability
    Fsm = make_fsm(a, [
        make_state(a, [make_transition(go, b)]),
        make_state(b, [make_transition(continue, c)]),
        make_state(c, [])
    ]),

    Result = cure_fsm_verifier:check_reachability_via_smt(Fsm, a, c),
    case Result of
        {reachable} ->
            % Expected
            ok;
        {unreachable} ->
            error({assertion_failed, "C should be reachable from A via SMT"});
        {error, Reason} ->
            % SMT might not be available - skip test
            io:format("Skipped (SMT error: ~p) ", [Reason]),
            ok
    end.

test_smt_invariant_holds() ->
    % Test SMT invariant checking (always_true should hold)
    Fsm = make_fsm(ready, [
        make_state(ready, [make_transition(start, processing)]),
        make_state(processing, [make_transition(complete, ready)])
    ]),

    Result = cure_fsm_verifier:check_state_invariant(Fsm, {always_true}),
    case Result of
        {ok, holds} ->
            % Expected: always_true holds
            ok;
        {violation, _} ->
            error({assertion_failed, "always_true should not be violated"});
        {error, Reason} ->
            % SMT might not be available - skip test
            io:format("Skipped (SMT error: ~p) ", [Reason]),
            ok
    end.

%% ============================================================================
%% Helper Functions
%% ============================================================================

make_fsm(InitialState, StateDefs) ->
    #fsm_def{
        name = test_fsm,
        states = [S#state_def.name || S <- StateDefs],
        initial = InitialState,
        state_defs = StateDefs,
        location = #location{}
    }.

make_state(Name, Transitions) ->
    #state_def{
        name = Name,
        transitions = Transitions,
        location = #location{}
    }.

make_transition(Event, Target) ->
    #transition{
        event = #identifier_expr{name = Event, location = #location{}},
        guard = undefined,
        target = Target,
        action = undefined,
        timeout = undefined,
        location = #location{}
    }.

%% Assertion helpers
assert_equals(Expected, Actual, Message) ->
    case Expected =:= Actual of
        true -> ok;
        false -> error({assertion_failed, {Message, {expected, Expected}, {actual, Actual}}})
    end.

assert_matches(Pattern, Value, Message) ->
    case match_pattern(Pattern, Value) of
        true -> ok;
        false -> error({assertion_failed, {Message, {pattern, Pattern}, {value, Value}}})
    end.

match_pattern({Tag, _}, {Tag, _}) ->
    true;
match_pattern(Pattern, Value) ->
    Pattern =:= Value.

assert_not_empty(List, Message) when is_list(List) ->
    case List of
        [] ->
            error({assertion_failed, {Message, {expected, non_empty_list}, {actual, empty_list}}});
        _ ->
            ok
    end;
assert_not_empty(_, Message) ->
    error({assertion_failed, {Message, not_a_list}}).

assert_contains(Pattern, List, Message) when is_list(List) ->
    Found = lists:any(
        fun(Element) ->
            match_pattern(Pattern, Element)
        end,
        List
    ),

    case Found of
        true -> ok;
        false -> error({assertion_failed, {Message, {pattern, Pattern}, {not_found_in, List}}})
    end;
assert_contains(_, _, Message) ->
    error({assertion_failed, {Message, not_a_list}}).
