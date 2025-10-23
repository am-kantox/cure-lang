-module(fsm_performance_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").
-include("../src/fsm/cure_fsm_runtime.hrl").

%% Test FSM performance optimizations
run() ->
    cure_utils:debug("=== Testing FSM Performance Optimizations ===~n"),

    Tests = [
        fun test_transition_lookup_performance/0,
        fun test_batch_event_processing/0,
        fun test_memory_optimization/0,
        fun test_registry_performance/0,
        fun test_concurrent_fsm_scaling/0,
        fun test_timeout_performance/0,
        fun benchmark_event_throughput/0,
        fun benchmark_fsm_creation_speed/0
    ],

    Results = lists:map(fun run_test/1, Tests),

    Passed = length([ok || ok <- Results]),
    Failed = length(Results) - Passed,

    cure_utils:debug("~nFSM Performance Tests Summary:~n"),
    cure_utils:debug("  Passed: ~w~n", [Passed]),
    cure_utils:debug("  Failed: ~w~n", [Failed]),

    case Failed of
        0 -> cure_utils:debug("All FSM performance tests passed!~n");
        _ -> cure_utils:debug("Some FSM performance tests failed.~n")
    end,

    {ok, #{passed => Passed, failed => Failed}}.

run_test(TestFun) ->
    TestName = extract_test_name(TestFun),
    cure_utils:debug("Running ~s... ", [TestName]),
    try
        TestFun(),
        cure_utils:debug("PASSED~n"),
        ok
    catch
        Error:Reason:Stack ->
            cure_utils:debug("FAILED~n"),
            cure_utils:debug("  Error: ~p:~p~n", [Error, Reason]),
            cure_utils:debug("  Stack: ~p~n", [Stack]),
            {error, Reason}
    end.

extract_test_name(Fun) ->
    {name, Name} = erlang:fun_info(Fun, name),
    atom_to_list(Name).

%% ============================================================================
%% Performance Test Cases
%% ============================================================================

test_transition_lookup_performance() ->
    % Create a complex FSM with many states and transitions
    ComplexFSM = create_complex_fsm_definition(),

    % Compile the FSM with optimized transitions
    CompiledFSM = cure_fsm_runtime:compile_fsm_definition(ComplexFSM),

    % Register the FSM
    cure_fsm_runtime:register_fsm_type(complex_fsm, CompiledFSM),

    % Start the FSM
    {ok, FSMPid} = cure_fsm_runtime:start_fsm(complex_fsm, undefined),

    % Benchmark transition lookup performance
    Events = [event1, event2, event3, event4, event5],

    % Time multiple lookups
    StartTime = erlang:monotonic_time(microsecond),

    % Send 1000 events to test transition performance
    lists:foreach(
        fun(_) ->
            lists:foreach(
                fun(Event) ->
                    cure_fsm_runtime:send_event(FSMPid, Event)
                end,
                Events
            )
        end,
        lists:seq(1, 200)
    ),

    EndTime = erlang:monotonic_time(microsecond),
    TotalTime = EndTime - StartTime,
    EventsProcessed = 1000,
    AvgTimePerEvent = TotalTime / EventsProcessed,

    cure_utils:debug(" [Avg: ~.2f μs/event] ", [AvgTimePerEvent]),

    % Cleanup
    cure_fsm_runtime:stop_fsm(FSMPid),
    cure_fsm_runtime:clear_fsm_registry(),

    % Performance assertion - should be under 5 microseconds per event
    true = AvgTimePerEvent < 5.0,

    ok.

test_batch_event_processing() ->
    % Create a simple FSM
    SimpleFSM = create_simple_fsm_definition(),
    CompiledFSM = cure_fsm_runtime:compile_fsm_definition(SimpleFSM),
    cure_fsm_runtime:register_fsm_type(batch_test_fsm, CompiledFSM),

    {ok, FSMPid} = cure_fsm_runtime:start_fsm(batch_test_fsm, undefined),

    % Test single event processing time
    Events = [event1, event2, event1, event2],

    StartTime1 = erlang:monotonic_time(microsecond),
    lists:foreach(
        fun(Event) ->
            cure_fsm_runtime:send_event(FSMPid, Event)
        end,
        Events
    ),
    % Wait for processing
    timer:sleep(10),
    EndTime1 = erlang:monotonic_time(microsecond),

    SingleEventTime = EndTime1 - StartTime1,

    % Test batch event processing time
    StartTime2 = erlang:monotonic_time(microsecond),
    cure_fsm_runtime:send_batch_events(FSMPid, Events),
    % Wait for processing
    timer:sleep(10),
    EndTime2 = erlang:monotonic_time(microsecond),

    BatchEventTime = EndTime2 - StartTime2,

    cure_utils:debug(" [Single: ~w μs, Batch: ~w μs] ", [SingleEventTime, BatchEventTime]),

    % Batch processing should be faster or at least not significantly slower
    true = BatchEventTime =< SingleEventTime * 1.5,

    % Cleanup
    cure_fsm_runtime:stop_fsm(FSMPid),
    cure_fsm_runtime:clear_fsm_registry(),

    ok.

test_memory_optimization() ->
    % Create FSM with history tracking
    FSM = create_history_fsm_definition(),
    CompiledFSM = cure_fsm_runtime:compile_fsm_definition(FSM),
    cure_fsm_runtime:register_fsm_type(memory_test_fsm, CompiledFSM),

    {ok, FSMPid} = cure_fsm_runtime:start_fsm(memory_test_fsm, undefined),

    % Get initial memory usage
    InitialMemory = process_info(FSMPid, memory),

    % Send many events to build up history
    Events = [event1, event2],
    lists:foreach(
        fun(_) ->
            lists:foreach(
                fun(Event) ->
                    cure_fsm_runtime:send_event(FSMPid, Event)
                end,
                Events
            )
        % 120 events total
        end,
        lists:seq(1, 60)
    ),

    % Wait for processing
    timer:sleep(100),

    % Get memory after many events
    FinalMemory = process_info(FSMPid, memory),

    cure_utils:debug(" [Memory: ~w -> ~w bytes] ", [InitialMemory, FinalMemory]),

    % Memory should be bounded due to history trimming
    {memory, InitialBytes} = InitialMemory,
    {memory, FinalBytes} = FinalMemory,
    MemoryGrowth = FinalBytes - InitialBytes,

    % Memory growth should be reasonable (less than 60KB for 120 events due to gen_server overhead)
    true = MemoryGrowth < 60000,

    % Cleanup
    cure_fsm_runtime:stop_fsm(FSMPid),
    cure_fsm_runtime:clear_fsm_registry(),

    ok.

test_registry_performance() ->
    % Test FSM type registration and lookup performance
    FSMTypes = [test_fsm_1, test_fsm_2, test_fsm_3, test_fsm_4, test_fsm_5],
    FSMDef = create_simple_fsm_definition(),
    CompiledFSM = cure_fsm_runtime:compile_fsm_definition(FSMDef),

    % Time registration of multiple FSM types
    StartTime = erlang:monotonic_time(microsecond),

    lists:foreach(
        fun(FSMType) ->
            cure_fsm_runtime:register_fsm_type(FSMType, CompiledFSM)
        end,
        FSMTypes
    ),

    EndTime = erlang:monotonic_time(microsecond),
    RegistrationTime = EndTime - StartTime,

    % Time lookup of FSM types
    StartLookup = erlang:monotonic_time(microsecond),

    % Perform 1000 lookups
    lists:foreach(
        fun(_) ->
            lists:foreach(
                fun(FSMType) ->
                    {ok, _} = cure_fsm_runtime:lookup_fsm_definition(FSMType)
                end,
                FSMTypes
            )
        end,
        lists:seq(1, 200)
    ),

    EndLookup = erlang:monotonic_time(microsecond),
    LookupTime = EndLookup - StartLookup,
    LookupsPerformed = 1000,
    AvgLookupTime = LookupTime / LookupsPerformed,

    cure_utils:debug(" [Reg: ~w μs, Lookup: ~.2f μs/op] ", [RegistrationTime, AvgLookupTime]),

    % Lookups should be very fast (under 1 microsecond)
    true = AvgLookupTime < 1.0,

    % Cleanup
    cure_fsm_runtime:clear_fsm_registry(),

    ok.

test_concurrent_fsm_scaling() ->
    % Test performance with multiple concurrent FSMs
    FSMDef = create_simple_fsm_definition(),
    CompiledFSM = cure_fsm_runtime:compile_fsm_definition(FSMDef),
    cure_fsm_runtime:register_fsm_type(concurrent_test_fsm, CompiledFSM),

    % Create multiple FSM instances
    NumFSMs = 50,
    StartTime = erlang:monotonic_time(microsecond),

    FSMPids = lists:map(
        fun(_) ->
            {ok, Pid} = cure_fsm_runtime:start_fsm(concurrent_test_fsm, undefined),
            Pid
        end,
        lists:seq(1, NumFSMs)
    ),

    CreateTime = erlang:monotonic_time(microsecond) - StartTime,

    % Send events to all FSMs concurrently
    EventStartTime = erlang:monotonic_time(microsecond),

    % Send events in parallel
    lists:foreach(
        fun(FSMPid) ->
            cure_fsm_runtime:send_event(FSMPid, event1),
            cure_fsm_runtime:send_event(FSMPid, event2)
        end,
        FSMPids
    ),

    % Wait for processing
    timer:sleep(100),
    EventEndTime = erlang:monotonic_time(microsecond),
    EventTime = EventEndTime - EventStartTime,

    cure_utils:debug(" [Create ~w FSMs: ~w μs, Events: ~w μs] ", [NumFSMs, CreateTime, EventTime]),

    % Creation should be fast (under 100 μs per FSM)
    AvgCreateTime = CreateTime / NumFSMs,
    true = AvgCreateTime < 100.0,

    % Cleanup
    lists:foreach(
        fun(FSMPid) ->
            cure_fsm_runtime:stop_fsm(FSMPid)
        end,
        FSMPids
    ),
    cure_fsm_runtime:clear_fsm_registry(),

    ok.

test_timeout_performance() ->
    % Test timeout handling performance
    TimeoutFSM = create_timeout_fsm_definition(),
    CompiledFSM = cure_fsm_runtime:compile_fsm_definition(TimeoutFSM),
    cure_fsm_runtime:register_fsm_type(timeout_test_fsm, CompiledFSM),

    {ok, FSMPid} = cure_fsm_runtime:start_fsm(timeout_test_fsm, undefined),

    % Measure timeout setting performance
    StartTime = erlang:monotonic_time(microsecond),

    % Set and clear timeouts multiple times
    lists:foreach(
        fun(_) ->
            cure_fsm_runtime:set_timeout(FSMPid, 1000, timeout_event),
            cure_fsm_runtime:clear_timeout(FSMPid)
        end,
        lists:seq(1, 100)
    ),

    EndTime = erlang:monotonic_time(microsecond),
    TotalTime = EndTime - StartTime,
    % 100 sets + 100 clears
    AvgTimeoutOpTime = TotalTime / 200,

    cure_utils:debug(" [Avg timeout op: ~.2f μs] ", [AvgTimeoutOpTime]),

    % Timeout operations should be fast
    true = AvgTimeoutOpTime < 10.0,

    % Cleanup
    cure_fsm_runtime:stop_fsm(FSMPid),
    cure_fsm_runtime:clear_fsm_registry(),

    ok.

benchmark_event_throughput() ->
    % Benchmark raw event throughput
    FSMDef = create_simple_fsm_definition(),
    CompiledFSM = cure_fsm_runtime:compile_fsm_definition(FSMDef),
    cure_fsm_runtime:register_fsm_type(throughput_test_fsm, CompiledFSM),

    {ok, FSMPid} = cure_fsm_runtime:start_fsm(throughput_test_fsm, undefined),

    % Send a large number of events and measure throughput
    NumEvents = 10000,
    Events = [event1, event2],

    StartTime = erlang:monotonic_time(microsecond),

    lists:foreach(
        fun(_) ->
            Event = lists:nth(rand:uniform(2), Events),
            cure_fsm_runtime:send_event(FSMPid, Event)
        end,
        lists:seq(1, NumEvents)
    ),

    % Wait for all events to be processed
    timer:sleep(1000),

    EndTime = erlang:monotonic_time(microsecond),
    TotalTime = EndTime - StartTime,
    EventsPerSecond = (NumEvents * 1000000) / TotalTime,

    cure_utils:debug(" [Throughput: ~w events/sec] ", [round(EventsPerSecond)]),

    % Should achieve at least 5K events per second
    true = EventsPerSecond > 5000,

    % Cleanup
    cure_fsm_runtime:stop_fsm(FSMPid),
    cure_fsm_runtime:clear_fsm_registry(),

    ok.

benchmark_fsm_creation_speed() ->
    % Benchmark FSM creation speed
    FSMDef = create_simple_fsm_definition(),
    CompiledFSM = cure_fsm_runtime:compile_fsm_definition(FSMDef),
    cure_fsm_runtime:register_fsm_type(creation_test_fsm, CompiledFSM),

    NumFSMs = 1000,

    StartTime = erlang:monotonic_time(microsecond),

    FSMPids = lists:map(
        fun(_) ->
            {ok, Pid} = cure_fsm_runtime:start_fsm(creation_test_fsm, undefined),
            Pid
        end,
        lists:seq(1, NumFSMs)
    ),

    EndTime = erlang:monotonic_time(microsecond),
    TotalTime = EndTime - StartTime,
    FSMsPerSecond = (NumFSMs * 1000000) / TotalTime,
    AvgCreationTime = TotalTime / NumFSMs,

    cure_utils:debug(" [Creation: ~w FSMs/sec, ~.2f μs/FSM] ", [
        round(FSMsPerSecond), AvgCreationTime
    ]),

    % Should create at least 10K FSMs per second
    true = FSMsPerSecond > 10000,

    % Cleanup
    lists:foreach(
        fun(FSMPid) ->
            cure_fsm_runtime:stop_fsm(FSMPid)
        end,
        FSMPids
    ),
    cure_fsm_runtime:clear_fsm_registry(),

    ok.

%% ============================================================================
%% Helper Functions for Creating Test FSM Definitions
%% ============================================================================

create_simple_fsm_definition() ->
    #fsm_def{
        name = simple_fsm,
        states = [state1, state2],
        initial = state1,
        state_defs = [
            #state_def{
                name = state1,
                transitions = [
                    #transition{
                        event = event1,
                        guard = undefined,
                        target = state2,
                        location = #location{line = 1, column = 1, file = "test"}
                    },
                    #transition{
                        event = event2,
                        guard = undefined,
                        target = state1,
                        location = #location{line = 1, column = 1, file = "test"}
                    }
                ],
                location = #location{line = 1, column = 1, file = "test"}
            },
            #state_def{
                name = state2,
                transitions = [
                    #transition{
                        event = event1,
                        guard = undefined,
                        target = state1,
                        location = #location{line = 1, column = 1, file = "test"}
                    },
                    #transition{
                        event = event2,
                        guard = undefined,
                        target = state2,
                        location = #location{line = 1, column = 1, file = "test"}
                    }
                ],
                location = #location{line = 1, column = 1, file = "test"}
            }
        ],
        location = #location{line = 1, column = 1, file = "test"}
    }.

create_complex_fsm_definition() ->
    % Create an FSM with many states and transitions for performance testing
    States = [state1, state2, state3, state4, state5, state6, state7, state8],
    Events = [event1, event2, event3, event4, event5],

    StateDefs = lists:map(
        fun(State) ->
            Transitions = lists:map(
                fun(Event) ->
                    % Round-robin to next state
                    NextStateIndex = (list_to_index(State, States) rem length(States)) + 1,
                    NextState = lists:nth(NextStateIndex, States),

                    #transition{
                        event = Event,
                        guard = undefined,
                        target = NextState,
                        location = #location{line = 1, column = 1, file = "test"}
                    }
                end,
                Events
            ),

            #state_def{
                name = State,
                transitions = Transitions,
                location = #location{line = 1, column = 1, file = "test"}
            }
        end,
        States
    ),

    #fsm_def{
        name = complex_fsm,
        states = States,
        initial = state1,
        state_defs = StateDefs,
        location = #location{line = 1, column = 1, file = "test"}
    }.

create_history_fsm_definition() ->
    % FSM that generates lots of events for memory testing
    #fsm_def{
        name = history_fsm,
        states = [active, idle],
        initial = active,
        state_defs = [
            #state_def{
                name = active,
                transitions = [
                    #transition{
                        event = event1,
                        guard = undefined,
                        target = idle,
                        location = #location{line = 1, column = 1, file = "test"}
                    },
                    #transition{
                        event = event2,
                        guard = undefined,
                        target = active,
                        location = #location{line = 1, column = 1, file = "test"}
                    }
                ],
                location = #location{line = 1, column = 1, file = "test"}
            },
            #state_def{
                name = idle,
                transitions = [
                    #transition{
                        event = event1,
                        guard = undefined,
                        target = active,
                        location = #location{line = 1, column = 1, file = "test"}
                    },
                    #transition{
                        event = event2,
                        guard = undefined,
                        target = idle,
                        location = #location{line = 1, column = 1, file = "test"}
                    }
                ],
                location = #location{line = 1, column = 1, file = "test"}
            }
        ],
        location = #location{line = 1, column = 1, file = "test"}
    }.

create_timeout_fsm_definition() ->
    #fsm_def{
        name = timeout_fsm,
        states = [waiting, ready],
        initial = waiting,
        state_defs = [
            #state_def{
                name = waiting,
                transitions = [
                    #transition{
                        event = {timeout, 1000},
                        guard = undefined,
                        target = ready,
                        location = #location{line = 1, column = 1, file = "test"}
                    }
                ],
                location = #location{line = 1, column = 1, file = "test"}
            },
            #state_def{
                name = ready,
                transitions = [
                    #transition{
                        event = reset,
                        guard = undefined,
                        target = waiting,
                        location = #location{line = 1, column = 1, file = "test"}
                    }
                ],
                location = #location{line = 1, column = 1, file = "test"}
            }
        ],
        location = #location{line = 1, column = 1, file = "test"}
    }.

%% Helper function to find index of element in list
list_to_index(Element, List) ->
    list_to_index(Element, List, 1).

list_to_index(Element, [Element | _], Index) ->
    Index;
list_to_index(Element, [_ | Rest], Index) ->
    list_to_index(Element, Rest, Index + 1);
list_to_index(_, [], _) ->
    % Default to 1 if not found
    1.
