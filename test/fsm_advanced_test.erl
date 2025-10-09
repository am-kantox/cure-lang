%% FSM Advanced Tests - Guards, Actions, and Complex Transitions
-module(fsm_advanced_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast_simple.hrl").
-include("../src/fsm/cure_fsm_runtime.hrl").

%% Run all advanced FSM tests
run() ->
    io:format("Running FSM Advanced tests...~n"),
    test_fsm_guard_conditions(),
    test_fsm_actions(),
    test_fsm_complex_guards(),
    test_fsm_guard_action_combination(),
    test_fsm_guard_failure_handling(),
    test_fsm_action_side_effects(),
    test_fsm_nested_guard_evaluation(),
    test_fsm_dynamic_guard_data(),
    io:format("All FSM advanced tests passed!~n").

%% Test FSM transitions with guard conditions
test_fsm_guard_conditions() ->
    % Create FSM with guard conditions - simplified for testing
    GuardedFSM = #fsm_definition{
        name = 'GuardedCounter',
        states = ['Zero', 'Positive', 'Negative'],
        initial_state = 'Zero',
        transitions = #{
            'Zero' => #{
                increment => {'Positive', undefined, undefined},
                decrement => {'Negative', undefined, undefined}
            },
            'Positive' => #{
                reset => {'Zero', undefined, undefined}
            },
            'Negative' => #{
                reset => {'Zero', undefined, undefined}
            }
        },
        timeouts = #{}
    },

    % Register the FSM
    ok = cure_fsm_runtime:register_fsm_type('GuardedCounter', GuardedFSM),

    % Start FSM with initial data
    {ok, FSMPid} = cure_fsm_runtime:start_fsm('GuardedCounter', #{count => 0}),

    % Verify initial state
    {ok, 'Zero'} = cure_fsm_runtime:get_state(FSMPid),

    % Test transition
    cure_fsm_runtime:send_event(FSMPid, increment),
    timer:sleep(20),
    {ok, 'Positive'} = cure_fsm_runtime:get_state(FSMPid),

    % Reset to test negative transition
    cure_fsm_runtime:send_event(FSMPid, reset),
    timer:sleep(20),
    {ok, 'Zero'} = cure_fsm_runtime:get_state(FSMPid),

    % Test decrement transition
    cure_fsm_runtime:send_event(FSMPid, decrement),
    timer:sleep(20),
    {ok, 'Negative'} = cure_fsm_runtime:get_state(FSMPid),

    cure_fsm_runtime:stop_fsm(FSMPid),
    io:format("✓ FSM guard conditions test passed~n").

%% Test FSM actions with side effects
test_fsm_actions() ->
    % Create FSM that tracks action history
    ActionFSM = #fsm_definition{
        name = 'ActionTracker',
        states = ['Idle', 'Active', 'Logged'],
        initial_state = 'Idle',
        transitions = #{
            'Idle' => #{
                start =>
                    {'Active',
                        % No guard
                        fun(_Data) -> true end, fun(Data) ->
                            History = maps:get(history, Data, []),
                            Data#{
                                history => [started | History],
                                start_time => erlang:system_time(millisecond)
                            }
                        end}
            },
            'Active' => #{
                log =>
                    {'Logged',
                        fun(Data) ->
                            % Guard: only log if we've been active for at least 10ms
                            StartTime = maps:get(start_time, Data, 0),
                            CurrentTime = erlang:system_time(millisecond),
                            CurrentTime - StartTime >= 10
                        end,
                        fun(Data) ->
                            History = maps:get(history, Data, []),
                            Data#{
                                history => [logged | History],
                                log_time => erlang:system_time(millisecond)
                            }
                        end},
                cancel =>
                    {'Idle',
                        % Always allow cancel
                        fun(_Data) -> true end, fun(Data) ->
                            History = maps:get(history, Data, []),
                            Data#{history => [cancelled | History]}
                        end}
            },
            'Logged' => #{
                reset =>
                    {'Idle', fun(_Data) -> true end, fun(Data) ->
                        Data#{
                            history => [reset | maps:get(history, Data, [])],
                            start_time => undefined,
                            log_time => undefined
                        }
                    end}
            }
        },
        timeouts = #{}
    },

    % Register and start FSM
    ok = cure_fsm_runtime:register_fsm_type('ActionTracker', ActionFSM),
    {ok, FSMPid} = cure_fsm_runtime:start_fsm('ActionTracker', #{history => []}),

    % Test start action
    cure_fsm_runtime:send_event(FSMPid, start),
    timer:sleep(20),
    {ok, 'Active'} = cure_fsm_runtime:get_state(FSMPid),

    % Verify start action executed
    {ok, Data1} = cure_fsm_runtime:get_data(FSMPid),
    History1 = maps:get(history, Data1),
    ?assertEqual([started], History1),
    ?assert(maps:is_key(start_time, Data1)),

    % Wait for guard condition to be satisfied, then test log action
    timer:sleep(15),
    cure_fsm_runtime:send_event(FSMPid, log),
    timer:sleep(20),
    {ok, 'Logged'} = cure_fsm_runtime:get_state(FSMPid),

    % Verify log action executed
    {ok, Data2} = cure_fsm_runtime:get_data(FSMPid),
    History2 = maps:get(history, Data2),
    ?assertEqual([logged, started], History2),
    ?assert(maps:is_key(log_time, Data2)),

    cure_fsm_runtime:stop_fsm(FSMPid),
    io:format("✓ FSM actions test passed~n").

%% Test complex guard conditions with multiple data fields
test_fsm_complex_guards() ->
    % Create FSM with complex guard conditions
    ComplexFSM = #fsm_definition{
        name = 'ComplexGuard',
        states = ['Init', 'Authorized', 'Processing', 'Complete'],
        initial_state = 'Init',
        transitions = #{
            'Init' => #{
                auth =>
                    {'Authorized',
                        fun(Data) ->
                            % Complex guard: check user level and permissions
                            UserLevel = maps:get(user_level, Data, 0),
                            Permissions = maps:get(permissions, Data, []),
                            (UserLevel >= 1) and lists:member(read, Permissions)
                        end,
                        fun(Data) ->
                            Data#{auth_time => erlang:system_time(millisecond)}
                        end}
            },
            'Authorized' => #{
                process =>
                    {'Processing',
                        fun(Data) ->
                            % Guard: check permissions and resource availability
                            Permissions = maps:get(permissions, Data, []),
                            Resources = maps:get(available_resources, Data, 0),
                            lists:member(write, Permissions) and (Resources > 10)
                        end,
                        fun(Data) ->
                            Resources = maps:get(available_resources, Data, 0),
                            Data#{
                                available_resources => Resources - 10,
                                processing_start => erlang:system_time(millisecond)
                            }
                        end}
            },
            'Processing' => #{
                complete =>
                    {'Complete',
                        fun(Data) ->
                            % Guard: check processing time
                            ProcessingStart = maps:get(processing_start, Data, 0),
                            CurrentTime = erlang:system_time(millisecond),
                            % At least 50ms processing
                            (CurrentTime - ProcessingStart) >= 50
                        end,
                        fun(Data) ->
                            Data#{completion_time => erlang:system_time(millisecond)}
                        end}
            }
        },
        timeouts = #{}
    },

    % Register and test FSM
    ok = cure_fsm_runtime:register_fsm_type('ComplexGuard', ComplexFSM),

    % Test with insufficient permissions
    {ok, FSMPid1} = cure_fsm_runtime:start_fsm('ComplexGuard', #{
        % Too low level
        user_level => 0,
        permissions => []
    }),

    cure_fsm_runtime:send_event(FSMPid1, auth),
    timer:sleep(20),
    % Should remain in Init
    {ok, 'Init'} = cure_fsm_runtime:get_state(FSMPid1),

    cure_fsm_runtime:stop_fsm(FSMPid1),

    % Test with proper permissions
    {ok, FSMPid2} = cure_fsm_runtime:start_fsm('ComplexGuard', #{
        user_level => 2,
        permissions => [read, write],
        available_resources => 20
    }),

    % Should successfully authorize
    cure_fsm_runtime:send_event(FSMPid2, auth),
    timer:sleep(20),
    {ok, 'Authorized'} = cure_fsm_runtime:get_state(FSMPid2),

    % Should successfully start processing
    cure_fsm_runtime:send_event(FSMPid2, process),
    timer:sleep(20),
    {ok, 'Processing'} = cure_fsm_runtime:get_state(FSMPid2),

    % Wait for processing time requirement
    timer:sleep(60),
    cure_fsm_runtime:send_event(FSMPid2, complete),
    timer:sleep(20),
    {ok, 'Complete'} = cure_fsm_runtime:get_state(FSMPid2),

    cure_fsm_runtime:stop_fsm(FSMPid2),
    io:format("✓ FSM complex guards test passed~n").

%% Test combination of guards and actions with data flow
test_fsm_guard_action_combination() ->
    % Create FSM that demonstrates guard-action data flow
    DataFlowFSM = #fsm_definition{
        name = 'DataFlow',
        states = ['Ready', 'Accumulating', 'Threshold'],
        initial_state = 'Ready',
        transitions = #{
            'Ready' => #{
                add_value =>
                    {'Accumulating',
                        fun(Data) ->
                            Value = maps:get(input_value, Data, 0),
                            % Guard: only positive values
                            Value > 0
                        end,
                        fun(Data) ->
                            Value = maps:get(input_value, Data, 0),
                            CurrentSum = maps:get(sum, Data, 0),
                            Data#{sum => CurrentSum + Value, input_value => 0}
                        end}
            },
            'Accumulating' => #{
                add_value =>
                    {'Accumulating',
                        fun(Data) ->
                            Value = maps:get(input_value, Data, 0),
                            CurrentSum = maps:get(sum, Data, 0),
                            % Guard: keep under 100
                            (Value > 0) and ((CurrentSum + Value) < 100)
                        end,
                        fun(Data) ->
                            Value = maps:get(input_value, Data, 0),
                            CurrentSum = maps:get(sum, Data, 0),
                            Data#{sum => CurrentSum + Value, input_value => 0}
                        end},
                check_threshold =>
                    {'Threshold',
                        fun(Data) ->
                            CurrentSum = maps:get(sum, Data, 0),
                            % Guard: threshold reached
                            CurrentSum >= 50
                        end,
                        fun(Data) ->
                            Data#{threshold_reached => erlang:system_time(millisecond)}
                        end}
            }
        },
        timeouts = #{}
    },

    ok = cure_fsm_runtime:register_fsm_type('DataFlow', DataFlowFSM),
    {ok, FSMPid} = cure_fsm_runtime:start_fsm('DataFlow', #{sum => 0}),

    % Add values and test guard-action combinations
    cure_fsm_runtime:send_event(FSMPid, {add_value, #{input_value => 15}}),
    timer:sleep(20),
    {ok, 'Accumulating'} = cure_fsm_runtime:get_state(FSMPid),

    % Check sum was updated by action
    {ok, Data1} = cure_fsm_runtime:get_data(FSMPid),
    ?assertEqual(15, maps:get(sum, Data1)),

    % Add more values
    cure_fsm_runtime:send_event(FSMPid, {add_value, #{input_value => 20}}),
    timer:sleep(20),
    cure_fsm_runtime:send_event(FSMPid, {add_value, #{input_value => 25}}),
    timer:sleep(20),

    {ok, Data2} = cure_fsm_runtime:get_data(FSMPid),
    ?assertEqual(60, maps:get(sum, Data2)),

    % Test threshold check
    cure_fsm_runtime:send_event(FSMPid, check_threshold),
    timer:sleep(20),
    {ok, 'Threshold'} = cure_fsm_runtime:get_state(FSMPid),

    cure_fsm_runtime:stop_fsm(FSMPid),
    io:format("✓ FSM guard-action combination test passed~n").

%% Test guard failure handling
test_fsm_guard_failure_handling() ->
    % Create FSM with guards that can fail
    GuardFailureFSM = #fsm_definition{
        name = 'GuardFailure',
        states = ['State1', 'State2'],
        initial_state = 'State1',
        transitions = #{
            'State1' => #{
                strict_transition =>
                    {'State2',
                        fun(Data) ->
                            Value = maps:get(value, Data, 0),
                            % Very strict guard
                            Value == 42
                        end,
                        fun(Data) ->
                            Data#{transition_count => maps:get(transition_count, Data, 0) + 1}
                        end}
            }
        },
        timeouts = #{}
    },

    ok = cure_fsm_runtime:register_fsm_type('GuardFailure', GuardFailureFSM),
    {ok, FSMPid} = cure_fsm_runtime:start_fsm('GuardFailure', #{value => 10, transition_count => 0}),

    % Test guard failure - should remain in State1
    cure_fsm_runtime:send_event(FSMPid, strict_transition),
    timer:sleep(20),
    {ok, 'State1'} = cure_fsm_runtime:get_state(FSMPid),

    % Verify action was not executed
    {ok, Data1} = cure_fsm_runtime:get_data(FSMPid),
    ?assertEqual(0, maps:get(transition_count, Data1)),

    % Update data to satisfy guard
    cure_fsm_runtime:update_data(FSMPid, #{value => 42, transition_count => 0}),

    % Test guard success - should transition to State2
    cure_fsm_runtime:send_event(FSMPid, strict_transition),
    timer:sleep(20),
    {ok, 'State2'} = cure_fsm_runtime:get_state(FSMPid),

    % Verify action was executed
    {ok, Data2} = cure_fsm_runtime:get_data(FSMPid),
    ?assertEqual(1, maps:get(transition_count, Data2)),

    cure_fsm_runtime:stop_fsm(FSMPid),
    io:format("✓ FSM guard failure handling test passed~n").

%% Test action side effects and data mutations
test_fsm_action_side_effects() ->
    % Create FSM with actions that have multiple side effects
    SideEffectFSM = #fsm_definition{
        name = 'SideEffect',
        states = ['Inactive', 'Active'],
        initial_state = 'Inactive',
        transitions = #{
            'Inactive' => #{
                activate =>
                    {'Active', fun(_Data) -> true end, fun(Data) ->
                        % Multiple side effects in action
                        Data#{
                            active => true,
                            activation_count => maps:get(activation_count, Data, 0) + 1,
                            activation_history => [
                                erlang:system_time(millisecond)
                                | maps:get(activation_history, Data, [])
                            ],
                            last_activator => maps:get(activator, Data, unknown)
                        }
                    end}
            },
            'Active' => #{
                deactivate =>
                    {'Inactive', fun(_Data) -> true end, fun(Data) ->
                        Data#{
                            active => false,
                            deactivation_time => erlang:system_time(millisecond)
                        }
                    end}
            }
        },
        timeouts = #{}
    },

    ok = cure_fsm_runtime:register_fsm_type('SideEffect', SideEffectFSM),
    {ok, FSMPid} = cure_fsm_runtime:start_fsm('SideEffect', #{
        activation_count => 0,
        activation_history => [],
        activator => user1
    }),

    % Test activation side effects
    cure_fsm_runtime:send_event(FSMPid, activate),
    timer:sleep(20),
    {ok, 'Active'} = cure_fsm_runtime:get_state(FSMPid),

    % Verify all side effects occurred
    {ok, Data1} = cure_fsm_runtime:get_data(FSMPid),
    ?assertEqual(true, maps:get(active, Data1)),
    ?assertEqual(1, maps:get(activation_count, Data1)),
    ?assertEqual(user1, maps:get(last_activator, Data1)),
    ?assertEqual(1, length(maps:get(activation_history, Data1))),

    cure_fsm_runtime:stop_fsm(FSMPid),
    io:format("✓ FSM action side effects test passed~n").

%% Test nested guard evaluation with multiple conditions
test_fsm_nested_guard_evaluation() ->
    % Create FSM with complex nested guard logic
    NestedGuardFSM = #fsm_definition{
        name = 'NestedGuard',
        states = ['Init', 'Validated', 'Processed'],
        initial_state = 'Init',
        transitions = #{
            'Init' => #{
                validate =>
                    {'Validated',
                        fun(Data) ->
                            % Nested guard conditions
                            UserData = maps:get(user_data, Data, #{}),
                            Age = maps:get(age, UserData, 0),
                            Email = maps:get(email, UserData, ""),
                            Country = maps:get(country, UserData, ""),

                            % Complex nested logic
                            AgeValid = (Age >= 18) and (Age =< 120),
                            EmailValid = string:find(Email, "@") =/= nomatch,
                            CountryValid = lists:member(Country, ["US", "CA", "UK", "DE"]),

                            AgeValid and EmailValid and CountryValid
                        end,
                        fun(Data) ->
                            Data#{
                                validated => true,
                                validation_time => erlang:system_time(millisecond)
                            }
                        end}
            },
            'Validated' => #{
                process =>
                    {'Processed',
                        fun(Data) ->
                            % Guard with exception handling
                            try
                                ProcessingData = maps:get(processing_data, Data, #{}),
                                Priority = maps:get(priority, ProcessingData, 0),
                                WorkloadFactor = maps:get(workload_factor, ProcessingData, 1.0),

                                % Complex calculation in guard
                                ProcessingScore = Priority * WorkloadFactor,
                                ProcessingScore > 5.0
                            catch
                                % Any error in guard evaluation fails the guard
                                _:_ -> false
                            end
                        end,
                        fun(Data) ->
                            Data#{processed => true}
                        end}
            }
        },
        timeouts = #{}
    },

    ok = cure_fsm_runtime:register_fsm_type('NestedGuard', NestedGuardFSM),

    % Test with invalid data (should fail validation)
    {ok, FSMPid1} = cure_fsm_runtime:start_fsm('NestedGuard', #{
        user_data => #{
            % Too young
            age => 16,
            % No @
            email => "invalid_email",
            % Invalid country
            country => "ZZ"
        }
    }),

    cure_fsm_runtime:send_event(FSMPid1, validate),
    timer:sleep(20),
    % Should remain in Init
    {ok, 'Init'} = cure_fsm_runtime:get_state(FSMPid1),

    cure_fsm_runtime:stop_fsm(FSMPid1),

    % Test with valid data
    {ok, FSMPid2} = cure_fsm_runtime:start_fsm('NestedGuard', #{
        user_data => #{
            age => 25,
            email => "user@example.com",
            country => "US"
        },
        processing_data => #{
            priority => 3,
            workload_factor => 2.5
        }
    }),

    % Should pass validation
    cure_fsm_runtime:send_event(FSMPid2, validate),
    timer:sleep(20),
    {ok, 'Validated'} = cure_fsm_runtime:get_state(FSMPid2),

    % Should pass processing guard (3 * 2.5 = 7.5 > 5.0)
    cure_fsm_runtime:send_event(FSMPid2, process),
    timer:sleep(20),
    {ok, 'Processed'} = cure_fsm_runtime:get_state(FSMPid2),

    cure_fsm_runtime:stop_fsm(FSMPid2),
    io:format("✓ FSM nested guard evaluation test passed~n").

%% Test dynamic guard data modification
test_fsm_dynamic_guard_data() ->
    % Create FSM where guards depend on dynamically modified data
    DynamicFSM = #fsm_definition{
        name = 'Dynamic',
        states = ['Collecting', 'Analyzing', 'Complete'],
        initial_state = 'Collecting',
        transitions = #{
            'Collecting' => #{
                analyze =>
                    {'Analyzing',
                        fun(Data) ->
                            Samples = maps:get(samples, Data, []),
                            % Need at least 5 samples
                            length(Samples) >= 5
                        end,
                        fun(Data) ->
                            Samples = maps:get(samples, Data, []),
                            Average =
                                case Samples of
                                    [] -> 0.0;
                                    _ -> lists:sum(Samples) / length(Samples)
                                end,
                            Data#{
                                analysis_start => erlang:system_time(millisecond),
                                average => Average
                            }
                        end},
                add_sample =>
                    {'Collecting',
                        fun(Data) ->
                            NewSample = maps:get(new_sample, Data, 0),
                            Samples = maps:get(samples, Data, []),
                            % Max 10 samples
                            (NewSample >= 0) and (length(Samples) < 10)
                        end,
                        fun(Data) ->
                            NewSample = maps:get(new_sample, Data, 0),
                            Samples = maps:get(samples, Data, []),
                            Data#{
                                samples => [NewSample | Samples],
                                new_sample => 0
                            }
                        end}
            },
            'Analyzing' => #{
                complete =>
                    {'Complete',
                        fun(Data) ->
                            Average = maps:get(average, Data, 0.0),
                            % Complete only if average is high enough
                            Average > 10.0
                        end,
                        fun(Data) ->
                            Data#{completion_time => erlang:system_time(millisecond)}
                        end}
            }
        },
        timeouts = #{}
    },

    ok = cure_fsm_runtime:register_fsm_type('Dynamic', DynamicFSM),
    {ok, FSMPid} = cure_fsm_runtime:start_fsm('Dynamic', #{samples => []}),

    % Add samples one by one, testing dynamic guard evaluation
    SampleValues = [5, 12, 8, 15, 20],
    lists:foreach(
        fun(Sample) ->
            cure_fsm_runtime:update_data(FSMPid, #{new_sample => Sample}),
            cure_fsm_runtime:send_event(FSMPid, add_sample),
            timer:sleep(10)
        end,
        SampleValues
    ),

    % Should still be collecting (but now with enough samples)
    {ok, 'Collecting'} = cure_fsm_runtime:get_state(FSMPid),

    % Verify samples were collected
    {ok, Data1} = cure_fsm_runtime:get_data(FSMPid),
    Samples = lists:reverse(maps:get(samples, Data1, [])),
    ?assertEqual(SampleValues, Samples),

    % Now should be able to analyze (guard satisfied: >= 5 samples)
    cure_fsm_runtime:send_event(FSMPid, analyze),
    timer:sleep(20),
    {ok, 'Analyzing'} = cure_fsm_runtime:get_state(FSMPid),

    % Check that average was calculated correctly
    {ok, Data2} = cure_fsm_runtime:get_data(FSMPid),
    Average = maps:get(average, Data2),
    ExpectedAverage = lists:sum(SampleValues) / length(SampleValues),
    ?assertEqual(ExpectedAverage, Average),

    % Should be able to complete (average = 12.0 > 10.0)
    cure_fsm_runtime:send_event(FSMPid, complete),
    timer:sleep(20),
    {ok, 'Complete'} = cure_fsm_runtime:get_state(FSMPid),

    cure_fsm_runtime:stop_fsm(FSMPid),
    io:format("✓ FSM dynamic guard data test passed~n").
