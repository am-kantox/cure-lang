%% Simplified FSM Tests - Compatible with actual runtime
-module(fsm_simple_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast.hrl").
-include("../src/fsm/cure_fsm_runtime.hrl").

%% Run all simplified FSM tests
run() ->
    cure_utils:debug("Running FSM Simple tests...~n"),
    test_basic_fsm_transitions(),
    test_fsm_registration(),
    test_fsm_state_queries(),
    cure_utils:debug("All FSM simple tests passed!~n").

%% Test basic FSM transitions
test_basic_fsm_transitions() ->
    % Create a simple FSM definition
    SimpleFSM = #fsm_definition{
        name = 'SimpleCounter',
        states = ['Zero', 'Positive', 'Negative'],
        initial_state = 'Zero',
        transitions = #{
            'Zero' => #{
                increment => {'Positive', undefined, undefined},
                decrement => {'Negative', undefined, undefined}
            },
            'Positive' => #{
                reset => {'Zero', undefined, undefined},
                increment => {'Positive', undefined, undefined}
            },
            'Negative' => #{
                reset => {'Zero', undefined, undefined},
                decrement => {'Negative', undefined, undefined}
            }
        },
        timeouts = #{}
    },

    % Register the FSM
    ok = cure_fsm_runtime:register_fsm_type('SimpleCounter', SimpleFSM),

    % Start FSM
    {ok, FSMPid} = cure_fsm_runtime:start_fsm('SimpleCounter', #{count => 0}),

    % Verify initial state
    {ok, 'Zero'} = cure_fsm_runtime:get_state(FSMPid),

    % Test increment transition
    cure_fsm_runtime:send_event(FSMPid, increment),
    timer:sleep(10),
    {ok, 'Positive'} = cure_fsm_runtime:get_state(FSMPid),

    % Test reset transition
    cure_fsm_runtime:send_event(FSMPid, reset),
    timer:sleep(10),
    {ok, 'Zero'} = cure_fsm_runtime:get_state(FSMPid),

    % Test decrement transition
    cure_fsm_runtime:send_event(FSMPid, decrement),
    timer:sleep(10),
    {ok, 'Negative'} = cure_fsm_runtime:get_state(FSMPid),

    % Clean up
    cure_fsm_runtime:stop_fsm(FSMPid),

    cure_utils:debug("✓ Basic FSM transitions test passed~n").

%% Test FSM registration and lookup
test_fsm_registration() ->
    % Create another FSM definition
    TestFSM = #fsm_definition{
        name = 'TestFSM',
        states = ['State1', 'State2'],
        initial_state = 'State1',
        transitions = #{
            'State1' => #{
                go => {'State2', undefined, undefined}
            },
            'State2' => #{
                back => {'State1', undefined, undefined}
            }
        },
        timeouts = #{}
    },

    % Register the FSM
    ok = cure_fsm_runtime:register_fsm_type('TestFSM', TestFSM),

    % Lookup the FSM
    {ok, Retrieved} = cure_fsm_runtime:lookup_fsm_definition('TestFSM'),
    ?assertEqual('TestFSM', Retrieved#fsm_definition.name),
    ?assertEqual(['State1', 'State2'], Retrieved#fsm_definition.states),
    ?assertEqual('State1', Retrieved#fsm_definition.initial_state),

    % Test lookup of non-existent FSM
    {error, not_found} = cure_fsm_runtime:lookup_fsm_definition('NonExistent'),

    cure_utils:debug("✓ FSM registration test passed~n").

%% Test FSM state queries and info
test_fsm_state_queries() ->
    % Reuse the SimpleFSM from first test
    SimpleFSM = #fsm_definition{
        name = 'QueryTest',
        states = ['A', 'B', 'C'],
        initial_state = 'A',
        transitions = #{
            'A' => #{
                go_b => {'B', undefined, undefined},
                go_c => {'C', undefined, undefined}
            },
            'B' => #{
                back => {'A', undefined, undefined}
            },
            'C' => #{
                back => {'A', undefined, undefined}
            }
        },
        timeouts = #{}
    },

    ok = cure_fsm_runtime:register_fsm_type('QueryTest', SimpleFSM),
    {ok, FSMPid} = cure_fsm_runtime:start_fsm('QueryTest', #{data => test}),

    % Test state queries
    {ok, 'A'} = cure_fsm_runtime:get_state(FSMPid),

    % Test FSM info
    {ok, Info} = cure_fsm_runtime:get_fsm_info(FSMPid),
    ?assertEqual('QueryTest', maps:get(fsm_type, Info)),
    ?assertEqual('A', maps:get(current_state, Info)),

    % Test some transitions
    cure_fsm_runtime:send_event(FSMPid, go_b),
    timer:sleep(10),
    {ok, 'B'} = cure_fsm_runtime:get_state(FSMPid),

    cure_fsm_runtime:send_event(FSMPid, back),
    timer:sleep(10),
    {ok, 'A'} = cure_fsm_runtime:get_state(FSMPid),

    cure_fsm_runtime:send_event(FSMPid, go_c),
    timer:sleep(10),
    {ok, 'C'} = cure_fsm_runtime:get_state(FSMPid),

    % Test performance stats
    {ok, _Stats} = cure_fsm_runtime:get_performance_stats(FSMPid),

    % Clean up
    cure_fsm_runtime:stop_fsm(FSMPid),

    cure_utils:debug("✓ FSM state queries test passed~n").
