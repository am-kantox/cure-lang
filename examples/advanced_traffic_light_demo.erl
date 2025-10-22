#!/usr/bin/env escript
%% -*- erlang -*-
%%! -pa ../_build/ebin

%%%-------------------------------------------------------------------
%%% @doc Advanced Traffic Light FSM Demo
%%% Demonstrates all FSM features including:
%%% - State transitions with guards
%%% - Action functions that modify state data and payload
%%% - Payload tracking across transitions
%%% - Timeout handling
%%% - Performance monitoring
%%% - Event history
%%% @end
%%%-------------------------------------------------------------------

-module(advanced_traffic_light_demo).
-include("../src/parser/cure_ast.hrl").
-include("../src/fsm/cure_fsm_runtime.hrl").

main(_Args) ->
    io:format("~n╔══════════════════════════════════════════════════════════════╗~n"),
    io:format("║  Advanced Traffic Light FSM Demo - Cure Programming Language ║~n"),
    io:format("╚══════════════════════════════════════════════════════════════╝~n~n"),
    
    %% Register the advanced traffic light FSM
    register_advanced_traffic_light(),
    
    %% Run the demo
    run_demo(),
    
    io:format("~n✓ Demo completed successfully!~n~n"),
    ok.

%% Register an advanced traffic light FSM with all features
register_advanced_traffic_light() ->
    io:format("📝 Registering Advanced Traffic Light FSM...~n"),
    
    %% Action for transitioning from Red to Green
    RedToGreenAction = fun(State, _Event) ->
        Data = State#fsm_state.data,
        Payload = case State#fsm_state.payload of
            undefined -> #{};
            P -> P
        end,
        
        %% Update state data - increment cycles when starting a new cycle (Red->Green)
        Cycles = maps:get(cycles_completed, Data, 0),
        NewData = maps:put(cycles_completed, Cycles + 1, Data),
        
        %% Update payload with transition info
        NewPayload = maps:put(last_transition, red_to_green, Payload),
        NewPayload2 = maps:put(transition_time, erlang:system_time(millisecond), NewPayload),
        NewPayload3 = maps:put(green_count, maps:get(green_count, NewPayload2, 0) + 1, NewPayload2),
        
        {NewData, NewPayload3}
    end,
    
    %% Action for transitioning from Green to Yellow
    GreenToYellowAction = fun(State, _Event) ->
        Data = State#fsm_state.data,
        Payload = case State#fsm_state.payload of
            undefined -> #{};
            P -> P
        end,
        
        %% Calculate how long we were in Green state
        LastTime = maps:get(transition_time, Payload, 0),
        CurrentTime = erlang:system_time(millisecond),
        Duration = CurrentTime - LastTime,
        
        %% Update payload with duration tracking
        NewPayload = maps:put(last_transition, green_to_yellow, Payload),
        NewPayload2 = maps:put(transition_time, CurrentTime, NewPayload),
        NewPayload3 = maps:put(green_duration, Duration, NewPayload2),
        NewPayload4 = maps:put(yellow_count, maps:get(yellow_count, NewPayload3, 0) + 1, NewPayload3),
        
        {Data, NewPayload4}
    end,
    
    %% Action for transitioning from Yellow to Red
    YellowToRedAction = fun(State, _Event) ->
        Data = State#fsm_state.data,
        Payload = case State#fsm_state.payload of
            undefined -> #{};
            P -> P
        end,
        
        %% Track yellow duration
        LastTime = maps:get(transition_time, Payload, 0),
        CurrentTime = erlang:system_time(millisecond),
        Duration = CurrentTime - LastTime,
        
        %% Update statistics
        TotalTransitions = maps:get(total_transitions, Data, 0),
        NewData = maps:put(total_transitions, TotalTransitions + 1, Data),
        
        %% Update payload
        NewPayload = maps:put(last_transition, yellow_to_red, Payload),
        NewPayload2 = maps:put(transition_time, CurrentTime, NewPayload),
        NewPayload3 = maps:put(yellow_duration, Duration, NewPayload2),
        NewPayload4 = maps:put(red_count, maps:get(red_count, NewPayload3, 0) + 1, NewPayload3),
        
        {NewData, NewPayload4}
    end,
    
    %% Action for emergency stop
    EmergencyAction = fun(State, Event) ->
        Data = State#fsm_state.data,
        Payload = case State#fsm_state.payload of
            undefined -> #{};
            P -> P
        end,
        
        EmergencyCount = maps:get(emergency_count, Data, 0),
        NewData = maps:put(emergency_count, EmergencyCount + 1, Data),
        
        %% Store emergency info in payload
        EventData = case Event of
            undefined -> #{};
            _ -> Event
        end,
        Reason = maps:get(reason, EventData, unknown),
        
        NewPayload = maps:put(last_emergency_reason, Reason, Payload),
        NewPayload2 = maps:put(emergency_time, erlang:system_time(millisecond), NewPayload),
        NewPayload3 = maps:put(emergency_from_state, State#fsm_state.current_state, NewPayload2),
        
        {NewData, NewPayload3}
    end,
    
    %% Guard to check if vehicle detected (from event data)
    VehicleDetectedGuard = fun(State, EventData) ->
        case EventData of
            #{vehicle_detected := true} -> 
                Count = maps:get(vehicle_count, State#fsm_state.data, 0),
                Count < 100;  %% Only proceed if not too many vehicles
            _ -> 
                true  %% Default: allow transition
        end
    end,
    
    %% Register FSM with all transitions
    ok = cure_fsm_runtime:register_fsm_type(
        advanced_traffic_light,
        ['Red', 'Green', 'Yellow', 'Maintenance'],
        'Red',
        [
            %% Red -> Green (with action)
            {'Red', timer, 'Green', undefined, RedToGreenAction},
            {'Red', emergency_stop, 'Maintenance', undefined, EmergencyAction},
            
            %% Green -> Yellow (with action and guard)
            {'Green', timer, 'Yellow', VehicleDetectedGuard, GreenToYellowAction},
            {'Green', emergency_stop, 'Maintenance', undefined, EmergencyAction},
            
            %% Yellow -> Red (with action)
            {'Yellow', timer, 'Red', undefined, YellowToRedAction},
            {'Yellow', emergency_stop, 'Maintenance', undefined, EmergencyAction},
            
            %% Maintenance -> Red
            {'Maintenance', resume, 'Red', undefined, fun(S, _E) ->
                Data = S#fsm_state.data,
                Payload = case S#fsm_state.payload of
                    undefined -> #{};
                    P -> P
                end,
                NewPayload = maps:put(maintenance_cleared, true, Payload),
                NewPayload2 = maps:put(resume_time, erlang:system_time(millisecond), NewPayload),
                {Data, NewPayload2}
            end}
        ]
    ),
    
    io:format("   ✓ FSM registered with 4 states and sophisticated actions~n~n").

%% Run the demonstration
run_demo() ->
    %% Start FSM instance
    io:format("🚦 Starting Traffic Light FSM...~n"),
    InitialData = #{
        cycles_completed => 0,
        total_transitions => 0,
        emergency_count => 0,
        vehicle_count => 0
    },
    {ok, FSM} = cure_fsm_runtime:start_fsm(advanced_traffic_light, InitialData),
    io:format("   ✓ FSM started with PID: ~p~n~n", [FSM]),
    
    %% Check initial state
    {ok, InitialState} = cure_fsm_runtime:get_state(FSM),
    io:format("📍 Initial State: ~p~n~n", [InitialState]),
    
    %% Simulate traffic light cycle
    io:format("🔄 Starting traffic light cycle...~n~n"),
    
    %% Red -> Green
    io:format("   [1] Sending 'timer' event (Red -> Green)~n"),
    cure_fsm_runtime:send_event(FSM, timer),
    timer:sleep(100),
    {ok, State1} = cure_fsm_runtime:get_state(FSM),
    io:format("       Current State: ~p~n", [State1]),
    print_fsm_info(FSM, "After Red->Green"),
    
    %% Green -> Yellow (with vehicle detected)
    io:format("~n   [2] Sending 'timer' event with vehicle data (Green -> Yellow)~n"),
    cure_fsm_runtime:send_event(FSM, timer, #{vehicle_detected => true}),
    timer:sleep(100),
    {ok, State2} = cure_fsm_runtime:get_state(FSM),
    io:format("       Current State: ~p~n", [State2]),
    print_fsm_info(FSM, "After Green->Yellow"),
    
    %% Yellow -> Red
    io:format("~n   [3] Sending 'timer' event (Yellow -> Red)~n"),
    cure_fsm_runtime:send_event(FSM, timer),
    timer:sleep(100),
    {ok, State3} = cure_fsm_runtime:get_state(FSM),
    io:format("       Current State: ~p~n", [State3]),
    print_fsm_info(FSM, "After Yellow->Red"),
    
    %% Complete another cycle
    io:format("~n   [4] Completing second cycle...~n"),
    cure_fsm_runtime:send_batch_events(FSM, [timer, timer, timer]),
    timer:sleep(100),
    {ok, State4} = cure_fsm_runtime:get_state(FSM),
    io:format("       Current State: ~p~n", [State4]),
    print_fsm_info(FSM, "After second cycle"),
    
    %% Emergency stop
    io:format("~n   [5] Triggering emergency stop~n"),
    cure_fsm_runtime:send_event(FSM, emergency_stop, #{reason => "Pedestrian detected"}),
    timer:sleep(100),
    {ok, State5} = cure_fsm_runtime:get_state(FSM),
    io:format("       Current State: ~p~n", [State5]),
    print_fsm_info(FSM, "After emergency stop"),
    
    %% Resume from maintenance
    io:format("~n   [6] Resuming from maintenance~n"),
    cure_fsm_runtime:send_event(FSM, resume),
    timer:sleep(100),
    {ok, State6} = cure_fsm_runtime:get_state(FSM),
    io:format("       Current State: ~p~n", [State6]),
    print_fsm_info(FSM, "After resume"),
    
    %% Give extra time for all events to process
    timer:sleep(200),
    
    %% Show final statistics
    io:format("~n~n═══════════════════════════════════════════════════════════~n"),
    io:format("📊 Final Statistics~n"),
    io:format("═══════════════════════════════════════════════════════════~n"),
    print_detailed_info(FSM),
    
    %% Performance stats
    {ok, PerfStats} = cure_fsm_runtime:get_performance_stats(FSM),
    io:format("~n⚡ Performance Metrics:~n"),
    io:format("   • Events Processed: ~p~n", [PerfStats#fsm_perf_stats.events_processed]),
    io:format("   • Avg Event Time: ~.2f μs~n", [float(PerfStats#fsm_perf_stats.avg_event_time)]),
    io:format("   • Max Event Time: ~.2f μs~n", [float(PerfStats#fsm_perf_stats.max_event_time)]),
    
    %% Clean up
    cure_fsm_runtime:stop_fsm(FSM),
    io:format("~n   ✓ FSM stopped~n").

%% Helper to print FSM info
print_fsm_info(FSM, Label) ->
    {ok, Info} = cure_fsm_runtime:get_fsm_info(FSM),
    Data = maps:get(data, Info),
    io:format("       ~s:~n", [Label]),
    io:format("         • Cycles: ~p~n", [maps:get(cycles_completed, Data, 0)]),
    io:format("         • Total Transitions: ~p~n", [maps:get(total_transitions, Data, 0)]),
    io:format("         • Emergencies: ~p~n", [maps:get(emergency_count, Data, 0)]).

%% Helper to print detailed info
print_detailed_info(FSM) ->
    {ok, Info} = cure_fsm_runtime:get_fsm_info(FSM),
    
    FSMType = maps:get(fsm_type, Info),
    CurrentState = maps:get(current_state, Info),
    Data = maps:get(data, Info),
    History = maps:get(event_history, Info),
    
    io:format("   FSM Type: ~p~n", [FSMType]),
    io:format("   Current State: ~p~n", [CurrentState]),
    io:format("~n   State Data:~n"),
    maps:fold(fun(K, V, _) ->
        io:format("     • ~p: ~p~n", [K, V])
    end, ok, Data),
    
    io:format("~n   Event History (last 5):~n"),
    RecentHistory = lists:sublist(History, 5),
    lists:foreach(fun({Event, From, To, _Time}) ->
        io:format("     • ~p: ~p -> ~p~n", [Event, From, To])
    end, RecentHistory).
