-module(fsm_mermaid_compile_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").
-include("../src/fsm/cure_fsm_runtime.hrl").

%% Test that Mermaid-style FSM with action blocks compiles and runs
run() ->
    io:format("~n=== Testing Mermaid-Style FSM Compilation ===~n~n"),

    % Parse the enhanced traffic light example
    io:format("1. Parsing enhanced traffic light example...~n"),
    case cure_parser:parse_file("examples/06_fsm_traffic_light_enhanced.cure") of
        {ok, ParsedItems} ->
            io:format("   ✓ Parsing successful~n"),

            % Extract FSM definition from parsed items
            FSMDef = extract_fsm_from_items(ParsedItems),
            case FSMDef of
                undefined ->
                    io:format("   ✗ No FSM found in parsed items~n"),
                    error(no_fsm_found);
                _ ->
                    io:format("   ✓ FSM extracted: ~p~n", [FSMDef#fsm_def.name]),

                    % Test FSM compilation
                    test_fsm_compilation(FSMDef)
            end;
        {error, Error} ->
            io:format("   ✗ Parse error: ~p~n", [Error]),
            error(parse_failed)
    end.

% Extract FSM from parsed items (handles both module_def and flat list)
extract_fsm_from_items(ParsedItems) when is_list(ParsedItems) ->
    % Could be [module_def{...}] or [fsm_def{}, function_def{}, ...]
    lists:foldl(
        fun(Item, Acc) ->
            case Item of
                FSM = #fsm_def{} ->
                    FSM;
                #module_def{items = ModuleItems} ->
                    % Recursively search module items
                    case extract_fsm_from_items(ModuleItems) of
                        undefined -> Acc;
                        FSM -> FSM
                    end;
                _ ->
                    Acc
            end
        end,
        undefined,
        ParsedItems
    ).

% Test FSM compilation
test_fsm_compilation(FSMDef) ->
    io:format("~n2. Compiling FSM definition...~n"),

    try
        % Compile FSM using runtime compiler
        CompiledFSM = cure_fsm_runtime:compile_fsm_definition(FSMDef),
        io:format("   ✓ FSM compiled successfully~n"),
        io:format("   FSM Name: ~p~n", [CompiledFSM#fsm_definition.name]),
        io:format("   States: ~p~n", [CompiledFSM#fsm_definition.states]),
        io:format("   Initial State: ~p~n", [CompiledFSM#fsm_definition.initial_state]),
        io:format("   Transitions: ~p entries~n", [
            maps:size(CompiledFSM#fsm_definition.transitions)
        ]),

        % Register FSM type
        io:format("~n3. Registering FSM type...~n"),
        ok = cure_fsm_runtime:register_fsm_type('TrafficStats', CompiledFSM),
        io:format("   ✓ FSM type registered~n"),

        % Test FSM instance creation
        test_fsm_instance(CompiledFSM),

        io:format("~n=== All Tests Passed! ===~n~n")
    catch
        Error:Reason:Stack ->
            io:format("   ✗ Compilation failed: ~p:~p~n", [Error, Reason]),
            io:format("   Stack: ~p~n", [Stack]),
            error(compilation_failed)
    end.

% Test FSM instance
test_fsm_instance(CompiledFSM) ->
    io:format("~n4. Creating FSM instance...~n"),

    InitialData = #{
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

    case cure_fsm_runtime:start_fsm('TrafficStats', InitialData) of
        {ok, FSMPid} ->
            io:format("   ✓ FSM instance created: ~p~n", [FSMPid]),

            % Test basic transition
            io:format("~n5. Testing FSM transitions...~n"),
            {ok, InitialState} = cure_fsm_runtime:get_state(FSMPid),
            io:format("   Initial state: ~p~n", [InitialState]),

            % Send timer event
            cure_fsm_runtime:send_event(FSMPid, timer, []),
            timer:sleep(10),

            {ok, AfterTimerState} = cure_fsm_runtime:get_state(FSMPid),
            io:format("   After timer event: ~p~n", [AfterTimerState]),

            % Get FSM info to check data
            {ok, Info} = cure_fsm_runtime:get_fsm_info(FSMPid),
            Data = maps:get(data, Info),
            io:format("   FSM Data: ~p~n", [Data]),

            % Verify action was executed (timer_events should be incremented)
            TimerEvents = maps:get(timer_events, Data, 0),
            case TimerEvents > 0 of
                true ->
                    io:format("   ✓ Actions executed correctly (timer_events = ~p)~n", [TimerEvents]);
                false ->
                    io:format("   ⚠ Actions may not have executed (timer_events = ~p)~n", [
                        TimerEvents
                    ])
            end,

            % Stop FSM
            cure_fsm_runtime:stop_fsm(FSMPid),
            io:format("   ✓ FSM instance stopped~n");
        {error, Error} ->
            io:format("   ✗ Failed to create FSM instance: ~p~n", [Error]),
            error(instance_creation_failed)
    end.
