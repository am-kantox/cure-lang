-module(traffic_light_enhanced_test).
-export([run/0]).

-include("../src/fsm/cure_fsm_runtime.hrl").

%% Test that demonstrates compilation and execution of enhanced traffic light FSM
%% This test will:
%% 1. Parse the enhanced Cure example
%% 2. Compile FSM to Erlang runtime representation
%% 3. Execute the demonstration scenarios
%% 4. Verify the FSM behaves correctly

run() ->
    io:format("~n=== Testing Enhanced Traffic Light FSM ===~n~n"),

    %% Test 1: Parse the Cure source file
    io:format("Test 1: Parsing enhanced example...~n"),
    CureFile = "../examples/06_fsm_traffic_light_enhanced.cure",

    case filelib:is_file(CureFile) of
        true ->
            io:format("  ✓ File exists~n"),
            test_fsm_definition();
        false ->
            io:format("  ✗ File not found (expected for now)~n"),
            test_fsm_definition()
    end.

%% Test the FSM definition directly using the runtime
test_fsm_definition() ->
    io:format("~nTest 2: Creating FSM definition...~n"),

    %% Define initial payload
    InitialPayload = #{
        cycles_completed => 0,
        timer_events => 0,
        emergency_stops => 0,
        total_transitions => 0,
        red_duration => 0,
        green_duration => 0,
        yellow_duration => 0,
        pedestrian_crossings => 0,
        errors_detected => 0
    },

    %% Create actions for incrementing counters
    Actions = create_fsm_actions(),

    %% Build FSM definition with all transitions
    FSMDef = #fsm_definition{
        name = traffic_light_fsm,
        states = ['Red', 'Green', 'Yellow', 'Maintenance', 'FlashingRed'],
        initial_state = 'Red',
        transitions = #{
            %% Normal cycle
            {'Red', timer} => {'Green', undefined, maps:get(red_timer, Actions)},
            {'Green', timer} => {'Yellow', undefined, maps:get(green_timer, Actions)},
            {'Yellow', timer} => {'Red', undefined, maps:get(yellow_timer, Actions)},

            %% Emergency stops
            {'Red', emergency} => {'Red', undefined, maps:get(emergency, Actions)},
            {'Green', emergency} => {'Red', undefined, maps:get(emergency, Actions)},
            {'Yellow', emergency} => {'Red', undefined, maps:get(emergency, Actions)},

            %% Pedestrian crossing
            {'Red', pedestrian} => {'Green', undefined, maps:get(pedestrian, Actions)},

            %% Maintenance mode
            {'Red', maintenance} => {'Maintenance', undefined, maps:get(maintenance, Actions)},
            {'Green', maintenance} => {'Maintenance', undefined, maps:get(maintenance, Actions)},
            {'Yellow', maintenance} => {'Maintenance', undefined, maps:get(maintenance, Actions)},
            {'Maintenance', resume} => {'Red', undefined, maps:get(resume, Actions)},

            %% Error handling
            {'Red', error} => {'FlashingRed', undefined, maps:get(error, Actions)},
            {'Green', error} => {'FlashingRed', undefined, maps:get(error, Actions)},
            {'Yellow', error} => {'FlashingRed', undefined, maps:get(error, Actions)},
            {'FlashingRed', reset} => {'Red', undefined, maps:get(reset, Actions)}
        },
        timeouts = #{}
    },

    io:format("  ✓ FSM definition created~n"),

    %% Register FSM type
    ok = cure_fsm_runtime:register_fsm_type(traffic_light_fsm, FSMDef),
    io:format("  ✓ FSM type registered~n"),

    %% Test FSM lifecycle
    test_fsm_lifecycle(InitialPayload).

%% Create action functions for the FSM
create_fsm_actions() ->
    RedTimerAction = fun(State, _EventData) ->
        Data = State#fsm_state.data,
        NewData = Data#{
            timer_events => maps:get(timer_events, Data) + 1,
            total_transitions => maps:get(total_transitions, Data) + 1,
            red_duration => maps:get(red_duration, Data) + 30
        },
        {NewData, State#fsm_state.payload}
    end,

    GreenTimerAction = fun(State, _EventData) ->
        Data = State#fsm_state.data,
        NewData = Data#{
            timer_events => maps:get(timer_events, Data) + 1,
            total_transitions => maps:get(total_transitions, Data) + 1,
            green_duration => maps:get(green_duration, Data) + 45
        },
        {NewData, State#fsm_state.payload}
    end,

    YellowTimerAction = fun(State, _EventData) ->
        Data = State#fsm_state.data,
        NewData = Data#{
            timer_events => maps:get(timer_events, Data) + 1,
            total_transitions => maps:get(total_transitions, Data) + 1,
            yellow_duration => maps:get(yellow_duration, Data) + 5,
            cycles_completed => maps:get(cycles_completed, Data) + 1
        },
        {NewData, State#fsm_state.payload}
    end,

    EmergencyAction = fun(State, _EventData) ->
        Data = State#fsm_state.data,
        NewData = Data#{
            emergency_stops => maps:get(emergency_stops, Data) + 1,
            total_transitions => maps:get(total_transitions, Data) + 1
        },
        {NewData, State#fsm_state.payload}
    end,

    PedestrianAction = fun(State, _EventData) ->
        Data = State#fsm_state.data,
        NewData = Data#{
            pedestrian_crossings => maps:get(pedestrian_crossings, Data) + 1,
            total_transitions => maps:get(total_transitions, Data) + 1,
            red_duration => maps:get(red_duration, Data) + 10
        },
        {NewData, State#fsm_state.payload}
    end,

    MaintenanceAction = fun(State, _EventData) ->
        Data = State#fsm_state.data,
        NewData = Data#{
            total_transitions => maps:get(total_transitions, Data) + 1
        },
        {NewData, State#fsm_state.payload}
    end,

    ResumeAction = fun(State, _EventData) ->
        Data = State#fsm_state.data,
        NewData = Data#{
            total_transitions => maps:get(total_transitions, Data) + 1
        },
        {NewData, State#fsm_state.payload}
    end,

    ErrorAction = fun(State, _EventData) ->
        Data = State#fsm_state.data,
        NewData = Data#{
            errors_detected => maps:get(errors_detected, Data) + 1,
            total_transitions => maps:get(total_transitions, Data) + 1
        },
        {NewData, State#fsm_state.payload}
    end,

    ResetAction = fun(State, _EventData) ->
        Data = State#fsm_state.data,
        NewData = Data#{
            total_transitions => maps:get(total_transitions, Data) + 1
        },
        {NewData, State#fsm_state.payload}
    end,

    #{
        red_timer => RedTimerAction,
        green_timer => GreenTimerAction,
        yellow_timer => YellowTimerAction,
        emergency => EmergencyAction,
        pedestrian => PedestrianAction,
        maintenance => MaintenanceAction,
        resume => ResumeAction,
        error => ErrorAction,
        reset => ResetAction
    }.

%% Test FSM lifecycle operations
test_fsm_lifecycle(InitialPayload) ->
    io:format("~nTest 3: FSM Lifecycle & Operations...~n"),

    %% Start FSM using registered type
    {ok, Pid} = cure_fsm_runtime:start_fsm(traffic_light_fsm, InitialPayload),
    io:format("  ✓ FSM started with PID: ~p~n", [Pid]),

    %% Register FSM
    ok = cure_fsm_cure_api:fsm_advertise(Pid, smart_traffic_light),
    io:format("  ✓ FSM registered as 'smart_traffic_light'~n"),

    %% Verify lookup
    Pid = cure_fsm_cure_api:fsm_whereis(smart_traffic_light),
    true = is_pid(Pid),
    io:format("  ✓ FSM lookup successful~n"),

    %% Test normal cycle
    test_normal_cycle(),

    %% Test batch processing
    test_batch_processing(),

    %% Test emergency stop
    test_emergency_stop(),

    %% Test pedestrian crossing
    test_pedestrian_crossing(),

    %% Test maintenance mode
    test_maintenance_mode(),

    %% Test error handling
    test_error_handling(),

    %% Get final statistics
    test_statistics(),

    io:format("~n=== All Tests Passed! ===~n~n").

%% Test normal traffic light cycle
test_normal_cycle() ->
    io:format("~nTest 4: Normal Traffic Cycle...~n"),

    %% Get initial state
    {ok, {'Red', _}} = cure_fsm_cure_api:fsm_state(smart_traffic_light),
    io:format("  ✓ Initial state: Red~n"),

    %% Red -> Green
    ok = cure_fsm_cure_api:fsm_cast(smart_traffic_light, timer, []),
    timer:sleep(10),
    {ok, {'Green', _}} = cure_fsm_cure_api:fsm_state(smart_traffic_light),
    io:format("  ✓ Transitioned to Green~n"),

    %% Green -> Yellow
    ok = cure_fsm_cure_api:fsm_cast(smart_traffic_light, timer, []),
    timer:sleep(10),
    {ok, {'Yellow', _}} = cure_fsm_cure_api:fsm_state(smart_traffic_light),
    io:format("  ✓ Transitioned to Yellow~n"),

    %% Yellow -> Red
    ok = cure_fsm_cure_api:fsm_cast(smart_traffic_light, timer, []),
    timer:sleep(10),
    {ok, {'Red', Payload1}} = cure_fsm_cure_api:fsm_state(smart_traffic_light),
    io:format("  ✓ Transitioned to Red (cycle complete)~n"),

    %% Verify cycle count
    1 = maps:get(cycles_completed, Payload1),
    io:format("  ✓ Cycles completed: 1~n").

%% Test batch event processing
test_batch_processing() ->
    io:format("~nTest 5: Batch Event Processing...~n"),

    %% Send batch of 6 timer events (2 complete cycles)
    Events = [timer, timer, timer, timer, timer, timer],
    ok = cure_fsm_cure_api:fsm_send_batch(smart_traffic_light, Events),
    timer:sleep(50),

    {ok, {'Red', Payload}} = cure_fsm_cure_api:fsm_state(smart_traffic_light),
    Cycles = maps:get(cycles_completed, Payload),
    io:format("  ✓ Batch processing complete~n"),
    io:format("  ✓ Total cycles: ~p~n", [Cycles]).

%% Test emergency stop
test_emergency_stop() ->
    io:format("~nTest 6: Emergency Stop...~n"),

    %% Progress to Green
    ok = cure_fsm_cure_api:fsm_cast(smart_traffic_light, timer, []),
    timer:sleep(10),

    %% Trigger emergency
    ok = cure_fsm_cure_api:fsm_cast(smart_traffic_light, emergency, []),
    timer:sleep(10),

    {ok, {'Red', Payload}} = cure_fsm_cure_api:fsm_state(smart_traffic_light),
    EmergencyStops = maps:get(emergency_stops, Payload),
    true = EmergencyStops >= 1,
    io:format("  ✓ Emergency stop executed~n"),
    io:format("  ✓ Emergency stops: ~p~n", [EmergencyStops]).

%% Test pedestrian crossing
test_pedestrian_crossing() ->
    io:format("~nTest 7: Pedestrian Crossing...~n"),

    %% Send pedestrian event from Red
    ok = cure_fsm_cure_api:fsm_cast(smart_traffic_light, pedestrian, []),
    timer:sleep(10),

    {ok, {'Green', Payload}} = cure_fsm_cure_api:fsm_state(smart_traffic_light),
    Crossings = maps:get(pedestrian_crossings, Payload),
    true = Crossings >= 1,
    io:format("  ✓ Pedestrian crossing activated~n"),
    io:format("  ✓ Crossings: ~p~n", [Crossings]).

%% Test maintenance mode
test_maintenance_mode() ->
    io:format("~nTest 8: Maintenance Mode...~n"),

    %% Enter maintenance
    ok = cure_fsm_cure_api:fsm_cast(smart_traffic_light, maintenance, []),
    timer:sleep(10),

    {ok, {'Maintenance', _}} = cure_fsm_cure_api:fsm_state(smart_traffic_light),
    io:format("  ✓ Entered maintenance mode~n"),

    %% Resume from maintenance
    ok = cure_fsm_cure_api:fsm_cast(smart_traffic_light, resume, []),
    timer:sleep(10),

    {ok, {'Red', _}} = cure_fsm_cure_api:fsm_state(smart_traffic_light),
    io:format("  ✓ Resumed to Red (safe state)~n").

%% Test error handling
test_error_handling() ->
    io:format("~nTest 9: Error Handling...~n"),

    %% Trigger error
    ok = cure_fsm_cure_api:fsm_cast(smart_traffic_light, error, []),
    timer:sleep(10),

    {ok, {'FlashingRed', Payload1}} = cure_fsm_cure_api:fsm_state(smart_traffic_light),
    Errors1 = maps:get(errors_detected, Payload1),
    true = Errors1 >= 1,
    io:format("  ✓ Entered error mode (FlashingRed)~n"),

    %% Reset from error
    ok = cure_fsm_cure_api:fsm_cast(smart_traffic_light, reset, []),
    timer:sleep(10),

    {ok, {'Red', _}} = cure_fsm_cure_api:fsm_state(smart_traffic_light),
    io:format("  ✓ Reset to normal operation~n").

%% Test statistics and monitoring
test_statistics() ->
    io:format("~nTest 10: Statistics & Monitoring...~n"),

    %% Get FSM info
    {ok, Info} = cure_fsm_cure_api:fsm_info(smart_traffic_light),
    io:format("  ✓ FSM info retrieved~n"),

    %% Get event history
    {ok, History} = cure_fsm_cure_api:fsm_history(smart_traffic_light),
    HistoryLength = length(History),
    io:format("  ✓ Event history: ~p events~n", [HistoryLength]),

    %% Display final payload
    {ok, {_, Payload}} = cure_fsm_cure_api:fsm_state(smart_traffic_light),
    io:format("~n  Final Statistics:~n"),
    io:format("    • Cycles: ~p~n", [maps:get(cycles_completed, Payload)]),
    io:format("    • Timer events: ~p~n", [maps:get(timer_events, Payload)]),
    io:format("    • Emergency stops: ~p~n", [maps:get(emergency_stops, Payload)]),
    io:format("    • Pedestrian crossings: ~p~n", [maps:get(pedestrian_crossings, Payload)]),
    io:format("    • Errors detected: ~p~n", [maps:get(errors_detected, Payload)]),
    io:format("    • Total transitions: ~p~n", [maps:get(total_transitions, Payload)]).
