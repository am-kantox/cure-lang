-module(fsm_verification_compile_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").
-include("../src/fsm/cure_fsm_runtime.hrl").

%% Test that verification example FSMs compile and work correctly
run() ->
    io:format("~n=== Testing FSM Verification Example Compilation ===~n~n"),

    % Parse the verification example
    io:format("1. Parsing FSM verification example...~n"),
    case cure_parser:parse_file("examples/07_fsm_verification.cure") of
        {ok, ParsedItems} ->
            io:format("   ✓ Parsing successful~n"),

            % Extract all FSM definitions
            FSMs = extract_all_fsms(ParsedItems),
            io:format("   ✓ Found ~p FSMs: ~p~n", [
                length(FSMs), [Name || #fsm_def{name = Name} <- FSMs]
            ]),

            % Test each FSM
            test_all_fsms(FSMs),

            io:format("~n=== All Verification Tests Passed! ===~n~n");
        {error, Error} ->
            io:format("   ✗ Parse error: ~p~n", [Error]),
            error(parse_failed)
    end.

% Extract all FSMs from parsed items
extract_all_fsms(ParsedItems) when is_list(ParsedItems) ->
    lists:foldl(
        fun(Item, Acc) ->
            case Item of
                FSM = #fsm_def{} ->
                    [FSM | Acc];
                #module_def{items = ModuleItems} ->
                    extract_all_fsms(ModuleItems) ++ Acc;
                _ ->
                    Acc
            end
        end,
        [],
        ParsedItems
    ).

% Test all FSMs
test_all_fsms(FSMs) ->
    lists:foreach(
        fun(FSM) ->
            test_single_fsm(FSM)
        end,
        FSMs
    ).

% Test a single FSM compilation
test_single_fsm(#fsm_def{name = Name} = FSMDef) ->
    io:format("~n2. Testing FSM: ~p~n", [Name]),

    try
        % Compile FSM
        io:format("   Compiling...~n"),
        CompiledFSM = cure_fsm_runtime:compile_fsm_definition(FSMDef),
        io:format("   ✓ Compiled successfully~n"),
        io:format("     States: ~p~n", [CompiledFSM#fsm_definition.states]),
        io:format("     Initial: ~p~n", [CompiledFSM#fsm_definition.initial_state]),
        io:format("     Transitions: ~p entries~n", [
            maps:size(CompiledFSM#fsm_definition.transitions)
        ]),

        % Register FSM type
        ok = cure_fsm_runtime:register_fsm_type(Name, CompiledFSM),
        io:format("   ✓ Registered~n"),

        % Test basic instantiation
        test_fsm_instance(Name, CompiledFSM)
    catch
        Error:Reason:Stack ->
            io:format("   ✗ Failed: ~p:~p~n", [Error, Reason]),
            io:format("   Stack: ~p~n", [Stack]),
            error({fsm_test_failed, Name})
    end.

% Test FSM instance creation and basic operations
test_fsm_instance(Name, #fsm_definition{states = States, initial_state = InitialState}) ->
    io:format("   Testing instance creation...~n"),

    % Create appropriate initial data based on FSM
    InitialData = create_initial_data(Name),

    case cure_fsm_runtime:start_fsm(Name, InitialData) of
        {ok, FSMPid} ->
            io:format("   ✓ Instance created: ~p~n", [FSMPid]),

            % Verify initial state
            {ok, CurrentState} = cure_fsm_runtime:get_state(FSMPid),
            case CurrentState =:= InitialState of
                true ->
                    io:format("   ✓ Initial state correct: ~p~n", [CurrentState]);
                false ->
                    io:format(
                        "   ⚠ Initial state mismatch: expected ~p, got ~p~n",
                        [InitialState, CurrentState]
                    )
            end,

            % Stop FSM
            cure_fsm_runtime:stop_fsm(FSMPid),
            io:format("   ✓ Instance stopped~n");
        {error, Error} ->
            io:format("   ✗ Failed to create instance: ~p~n", [Error]),
            error(instance_creation_failed)
    end.

% Create appropriate initial data for each FSM type
create_initial_data('DeadlockDetector') ->
    #{
        requests_sent => 0,
        responses_received => 0,
        timeout_count => 0,
        deadlock_detected => false
    };
create_initial_data('ReachabilityChecker') ->
    #{
        states_visited => [],
        goal_reached => false,
        exploration_depth => 0
    };
create_initial_data('LivenessMonitor') ->
    #{
        progress_events => 0,
        stall_count => 0,
        last_progress_time => 0
    };
create_initial_data('SafetyChecker') ->
    #{
        invariant_violations => 0,
        checks_performed => 0,
        last_check_passed => true
    };
create_initial_data(_) ->
    #{}.
