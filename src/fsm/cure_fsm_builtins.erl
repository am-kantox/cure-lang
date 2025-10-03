%% Cure Programming Language - FSM Built-in Functions
%% High-level FSM functions available in Cure programs
-module(cure_fsm_builtins).

%% Export built-in FSM functions
-export([
    % FSM lifecycle
    fsm_spawn/1, fsm_spawn/2,
    fsm_stop/1,
    
    % FSM operations
    fsm_send/2, fsm_send/3,
    fsm_state/1,
    fsm_info/1,
    
    % FSM utilities
    fsm_is_alive/1,
    fsm_monitor/1,
    fsm_link/1,
    
    % FSM synchronization
    fsm_call/2, fsm_call/3,
    fsm_wait_state/2, fsm_wait_state/3,
    
    % FSM inspection (for debugging)
    fsm_history/1,
    fsm_dump_state/1,
    
    % Integration functions
    register_fsm_builtins/1,
    register_module_fsms/1,
    validate_fsm_type/1,
    validate_fsm_event/2
]).

%% Include AST definitions for type checking
-include("../parser/cure_ast_simple.hrl").

%% Include FSM runtime records
-record(fsm_definition, {
    name,             % FSM type name
    states,           % List of valid states
    initial_state,    % Initial state
    transitions,      % Transition table: #{State => #{Event => {Target, Guard, Action}}}
    timeouts          % Timeout table: #{State => {Timeout, Event}}
}).

%% ============================================================================
%% FSM Lifecycle Functions
%% ============================================================================

%% Spawn a new FSM instance with default initial data
fsm_spawn(FSMType) ->
    fsm_spawn(FSMType, undefined).

%% Spawn a new FSM instance with initial data
fsm_spawn(FSMType, InitialData) when is_atom(FSMType) ->
    case cure_fsm_runtime:start_fsm(FSMType, InitialData) of
        {ok, Pid} ->
            {ok, Pid};
        {error, Reason} ->
            {error, Reason}
    end;
fsm_spawn(FSMType, _InitialData) ->
    {error, {invalid_fsm_type, FSMType}}.

%% Stop an FSM instance
fsm_stop(FSMPid) when is_pid(FSMPid) ->
    case cure_fsm_runtime:stop_fsm(FSMPid) of
        ok -> ok;
        {error, Reason} -> {error, Reason}
    end;
fsm_stop(FSM) ->
    {error, {invalid_fsm_pid, FSM}}.

%% ============================================================================
%% FSM Operations
%% ============================================================================

%% Send an event to an FSM (asynchronous)
fsm_send(FSMPid, Event) when is_pid(FSMPid) ->
    cure_fsm_runtime:send_event(FSMPid, Event),
    ok;
fsm_send(FSM, _Event) ->
    {error, {invalid_fsm_pid, FSM}}.

%% Send an event with data to an FSM (asynchronous)
fsm_send(FSMPid, Event, Data) when is_pid(FSMPid) ->
    cure_fsm_runtime:send_event(FSMPid, Event, Data),
    ok;
fsm_send(FSM, _Event, _Data) ->
    {error, {invalid_fsm_pid, FSM}}.

%% Get the current state of an FSM
fsm_state(FSMPid) when is_pid(FSMPid) ->
    case cure_fsm_runtime:get_state(FSMPid) of
        {ok, State} -> {ok, State};
        {error, Reason} -> {error, Reason}
    end;
fsm_state(FSM) ->
    {error, {invalid_fsm_pid, FSM}}.

%% Get detailed information about an FSM
fsm_info(FSMPid) when is_pid(FSMPid) ->
    case cure_fsm_runtime:get_fsm_info(FSMPid) of
        {ok, Info} -> {ok, Info};
        {error, Reason} -> {error, Reason}
    end;
fsm_info(FSM) ->
    {error, {invalid_fsm_pid, FSM}}.

%% ============================================================================
%% FSM Utilities
%% ============================================================================

%% Check if an FSM is still alive
fsm_is_alive(FSMPid) when is_pid(FSMPid) ->
    erlang:is_process_alive(FSMPid);
fsm_is_alive(_) ->
    false.

%% Monitor an FSM for termination
fsm_monitor(FSMPid) when is_pid(FSMPid) ->
    MonitorRef = erlang:monitor(process, FSMPid),
    {ok, MonitorRef};
fsm_monitor(FSM) ->
    {error, {invalid_fsm_pid, FSM}}.

%% Link to an FSM (bidirectional crash propagation)
fsm_link(FSMPid) when is_pid(FSMPid) ->
    try
        erlang:link(FSMPid),
        ok
    catch
        error:noproc -> {error, fsm_dead};
        error:Reason -> {error, Reason}
    end;
fsm_link(FSM) ->
    {error, {invalid_fsm_pid, FSM}}.

%% ============================================================================
%% FSM Synchronization
%% ============================================================================

%% Send an event and wait for a response (synchronous, with default timeout)
fsm_call(FSMPid, Event) ->
    fsm_call(FSMPid, Event, 5000).

%% Send an event and wait for a response with timeout
fsm_call(FSMPid, Event, Timeout) when is_pid(FSMPid), is_integer(Timeout), Timeout > 0 ->
    % Send event asynchronously
    ok = fsm_send(FSMPid, Event),
    
    % Wait for state change or timeout
    InitialState = case fsm_state(FSMPid) of
        {ok, State} -> State;
        {error, _} -> undefined
    end,
    
    wait_for_state_change(FSMPid, InitialState, Timeout);

fsm_call(FSM, _Event, _Timeout) ->
    {error, {invalid_fsm_pid, FSM}}.

%% Wait for FSM to reach a specific state
fsm_wait_state(FSMPid, TargetState) ->
    fsm_wait_state(FSMPid, TargetState, 5000).

fsm_wait_state(FSMPid, TargetState, Timeout) when is_pid(FSMPid), is_atom(TargetState) ->
    case fsm_state(FSMPid) of
        {ok, TargetState} -> 
            {ok, TargetState};
        {ok, _OtherState} ->
            wait_for_target_state(FSMPid, TargetState, Timeout);
        {error, Reason} ->
            {error, Reason}
    end;

fsm_wait_state(FSM, _TargetState, _Timeout) ->
    {error, {invalid_fsm_pid, FSM}}.

%% ============================================================================
%% FSM Inspection (for debugging)
%% ============================================================================

%% Get the event history of an FSM
fsm_history(FSMPid) when is_pid(FSMPid) ->
    case fsm_info(FSMPid) of
        {ok, #{event_history := History}} -> {ok, History};
        {ok, _Info} -> {ok, []};
        {error, Reason} -> {error, Reason}
    end;
fsm_history(FSM) ->
    {error, {invalid_fsm_pid, FSM}}.

%% Dump the complete state of an FSM (for debugging)
fsm_dump_state(FSMPid) when is_pid(FSMPid) ->
    try
        State = sys:get_state(FSMPid),
        {ok, State}
    catch
        exit:Reason -> {error, Reason}
    end;
fsm_dump_state(FSM) ->
    {error, {invalid_fsm_pid, FSM}}.

%% ============================================================================
%% Internal Helper Functions
%% ============================================================================

%% Wait for any state change
wait_for_state_change(FSMPid, InitialState, Timeout) ->
    StartTime = erlang:system_time(millisecond),
    wait_for_change_loop(FSMPid, InitialState, StartTime, Timeout).

wait_for_change_loop(FSMPid, InitialState, StartTime, Timeout) ->
    CurrentTime = erlang:system_time(millisecond),
    
    if
        CurrentTime - StartTime >= Timeout ->
            {error, timeout};
        true ->
            case fsm_state(FSMPid) of
                {ok, InitialState} ->
                    % Still in same state, sleep and retry
                    timer:sleep(10),
                    wait_for_change_loop(FSMPid, InitialState, StartTime, Timeout);
                {ok, NewState} ->
                    % State changed
                    {ok, NewState};
                {error, Reason} ->
                    {error, Reason}
            end
    end.

%% Wait for a specific target state
wait_for_target_state(FSMPid, TargetState, Timeout) ->
    StartTime = erlang:system_time(millisecond),
    wait_for_target_loop(FSMPid, TargetState, StartTime, Timeout).

wait_for_target_loop(FSMPid, TargetState, StartTime, Timeout) ->
    CurrentTime = erlang:system_time(millisecond),
    
    if
        CurrentTime - StartTime >= Timeout ->
            {error, timeout};
        true ->
            case fsm_state(FSMPid) of
                {ok, TargetState} ->
                    {ok, TargetState};
                {ok, _OtherState} ->
                    % Not target state yet, sleep and retry
                    timer:sleep(10),
                    wait_for_target_loop(FSMPid, TargetState, StartTime, Timeout);
                {error, Reason} ->
                    {error, Reason}
            end
    end.

%% ============================================================================
%% Integration with Type System
%% ============================================================================

%% Function to register FSM built-ins with the type system

register_fsm_builtins(TypeEnv) ->
    % Add FSM built-in functions to type environment
    
    % fsm_spawn/1,2
    FSMSpawn1Type = {function_type, [{primitive_type, 'Atom'}], {fsm_type}},
    FSMSpawn2Type = {function_type, [{primitive_type, 'Atom'}, {any_type}], {fsm_type}},
    
    % fsm_send/2,3
    FSMSend2Type = {function_type, [{fsm_type}, {any_type}], {primitive_type, 'Atom'}},
    FSMSend3Type = {function_type, [{fsm_type}, {any_type}, {any_type}], {primitive_type, 'Atom'}},
    
    % fsm_state/1
    FSMStateType = {function_type, [{fsm_type}], {union_type, [{primitive_type, 'Atom'}, {error_type}]}},
    
    % fsm_stop/1
    FSMStopType = {function_type, [{fsm_type}], {union_type, [{primitive_type, 'Atom'}, {error_type}]}},
    
    % Register all built-in functions
    Functions = [
        {fsm_spawn, FSMSpawn1Type},
        {fsm_send, FSMSend2Type},
        {fsm_state, FSMStateType},
        {fsm_stop, FSMStopType}
        % TODO: Add types for all other functions
    ],
    
    lists:foldl(fun({Name, Type}, Env) ->
        cure_types:extend_env(Env, Name, Type)
    end, TypeEnv, Functions).

%% ============================================================================
%% Compiler Integration Functions
%% ============================================================================

%% Function to be called during module compilation to register FSM definitions

register_module_fsms(ModuleAST) ->
    FSMDefs = extract_fsm_definitions(ModuleAST),
    lists:foreach(fun(FSMDef) ->
        CompiledDef = cure_fsm_runtime:compile_fsm_definition(FSMDef),
        cure_fsm_runtime:register_fsm_definition(FSMDef#fsm_def.name, CompiledDef)
    end, FSMDefs),
    ok.

%% Extract FSM definitions from module AST
extract_fsm_definitions(ModuleAST) when is_list(ModuleAST) ->
    lists:filtermap(fun(Item) ->
        case Item of
            #fsm_def{} -> {true, Item};
            _ -> false
        end
    end, ModuleAST);

extract_fsm_definitions(#module_def{items = Items}) ->
    extract_fsm_definitions(Items);

extract_fsm_definitions(_) ->
    [].

%% ============================================================================
%% Error Handling and Validation
%% ============================================================================

%% Validate FSM type exists before spawning

validate_fsm_type(FSMType) when is_atom(FSMType) ->
    case cure_fsm_runtime:lookup_fsm_definition(FSMType) of
        {ok, _Definition} -> ok;
        {error, not_found} -> {error, {fsm_type_not_found, FSMType}}
    end;
validate_fsm_type(FSMType) ->
    {error, {invalid_fsm_type, FSMType}}.

%% Validate event is appropriate for FSM

validate_fsm_event(FSMPid, Event) when is_pid(FSMPid) ->
    case fsm_info(FSMPid) of
        {ok, #{fsm_type := FSMType, current_state := CurrentState}} ->
            case cure_fsm_runtime:lookup_fsm_definition(FSMType) of
                {ok, Definition} ->
                    validate_event_for_state(Definition, CurrentState, Event);
                {error, not_found} ->
                    {error, fsm_definition_not_found}
            end;
        {error, Reason} ->
            {error, Reason}
    end;
validate_fsm_event(FSM, _Event) ->
    {error, {invalid_fsm_pid, FSM}}.

%% Internal validation helper
validate_event_for_state(Definition, State, Event) ->
    Transitions = Definition#fsm_definition.transitions,
    case maps:get(State, Transitions, #{}) of
        StateTransitions when is_map(StateTransitions) ->
            case maps:is_key(Event, StateTransitions) of
                true -> ok;
                false -> {warning, event_not_handled}
            end;
        _ ->
            {error, invalid_state}
    end.