%% Cure Programming Language - FSM Built-in Functions
%% High-level FSM functions available in Cure programs
-module(cure_fsm_builtins).

-moduledoc """
# Cure Programming Language - FSM Built-in Functions

This module provides built-in FSM functions that interface directly with the
cure_fsm_runtime module. These functions are called from Cure programs via
the FFI (Foreign Function Interface) to provide FSM functionality.

## Features

### FSM Lifecycle Management
- **FSM Spawning**: Create new FSM instances with type validation
- **FSM Termination**: Graceful shutdown of FSM processes

### FSM Operations
- **Event Sending**: Asynchronous event dispatch to FSMs
- **State Inspection**: Query current FSM state and information
- **Batch Operations**: Efficient batch event processing

### FSM Utilities
- **Process Monitoring**: Monitor FSM processes for termination
- **Process Linking**: Bidirectional crash propagation
- **Timeout Management**: Set and clear FSM timeouts

## API Design

All functions are designed to be called from Cure programs via FFI.
They provide a clean interface to the underlying Erlang FSM runtime.
""".

%% Export FSM built-in functions for FFI
-export([
    % FSM lifecycle
    fsm_spawn/2,
    fsm_spawn_with_options/3,
    fsm_stop/1,

    % FSM operations
    fsm_send/2,
    fsm_send/3,
    fsm_send_batch/2,
    fsm_state/1,
    fsm_info/1,
    fsm_history/1,
    fsm_set_data/2,
    fsm_get_performance_stats/1,
    fsm_reset_stats/1,

    % FSM utilities
    fsm_is_alive/1,
    fsm_monitor/1,
    fsm_link/1,
    fsm_unlink/1,
    fsm_set_timeout/3,
    fsm_clear_timeout/1,

    % FSM validation and introspection
    fsm_validate_type/1,
    fsm_validate_event/2,
    fsm_get_registered_types/0,
    fsm_lookup_definition/1,

    % Legacy compatibility (for tests)
    validate_fsm_type/1,
    validate_fsm_event/2
]).

%% Include FSM runtime records
-include("cure_fsm_runtime.hrl").

%% ============================================================================
%% FSM Lifecycle Functions
%% ============================================================================

%% Spawn FSM instance
fsm_spawn(FSMType, InitialData) when is_atom(FSMType) ->
    case cure_fsm_runtime:start_fsm(FSMType, InitialData) of
        {ok, Pid} ->
            Pid;
        {error, Reason} ->
            {error, Reason}
    end;
fsm_spawn(FSMType, _InitialData) ->
    {error, {invalid_fsm_type, FSMType}}.

%% Spawn FSM instance with options
fsm_spawn_with_options(FSMType, InitialData, Options) when is_atom(FSMType) ->
    case cure_fsm_runtime:start_fsm(FSMType, InitialData, Options) of
        {ok, Pid} ->
            Pid;
        {error, Reason} ->
            {error, Reason}
    end;
fsm_spawn_with_options(FSMType, _InitialData, _Options) ->
    {error, {invalid_fsm_type, FSMType}}.

%% Stop FSM instance
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

%% Send event to FSM
fsm_send(FSMPid, Event) when is_pid(FSMPid) ->
    cure_fsm_runtime:send_event(FSMPid, Event),
    ok;
fsm_send(FSM, _Event) ->
    {error, {invalid_fsm_pid, FSM}}.

%% Send event with data to FSM
fsm_send(FSMPid, Event, Data) when is_pid(FSMPid) ->
    cure_fsm_runtime:send_event(FSMPid, Event, Data),
    ok;
fsm_send(FSM, _Event, _Data) ->
    {error, {invalid_fsm_pid, FSM}}.

%% Send batch events to FSM
fsm_send_batch(FSMPid, Events) when is_pid(FSMPid), is_list(Events) ->
    cure_fsm_runtime:send_batch_events(FSMPid, Events),
    ok;
fsm_send_batch(FSM, _Events) ->
    {error, {invalid_fsm_pid, FSM}}.

%% Get current FSM state
fsm_state(FSMPid) when is_pid(FSMPid) ->
    case cure_fsm_runtime:get_state(FSMPid) of
        {ok, State} -> State;
        {error, Reason} -> {error, Reason}
    end;
fsm_state(FSM) ->
    {error, {invalid_fsm_pid, FSM}}.

%% Get FSM information
fsm_info(FSMPid) when is_pid(FSMPid) ->
    case cure_fsm_runtime:get_fsm_info(FSMPid) of
        {ok, Info} -> {ok, Info};
        {error, Reason} -> {error, Reason}
    end;
fsm_info(FSM) ->
    {error, {invalid_fsm_pid, FSM}}.

%% Get FSM event history
fsm_history(FSMPid) when is_pid(FSMPid) ->
    case fsm_info(FSMPid) of
        {ok, #{event_history := History}} -> History;
        {ok, _Info} -> [];
        {error, Reason} -> {error, Reason}
    end;
fsm_history(FSM) ->
    {error, {invalid_fsm_pid, FSM}}.

%% Set FSM data
fsm_set_data(FSMPid, NewData) when is_pid(FSMPid) ->
    % This could be extended to actually set data in the runtime
    ok;
fsm_set_data(FSM, _NewData) ->
    {error, {invalid_fsm_pid, FSM}}.

%% Get FSM performance statistics
fsm_get_performance_stats(FSMPid) when is_pid(FSMPid) ->
    case cure_fsm_runtime:get_performance_stats(FSMPid) of
        {ok, Stats} -> {ok, Stats};
        {error, Reason} -> {error, Reason}
    end;
fsm_get_performance_stats(FSM) ->
    {error, {invalid_fsm_pid, FSM}}.

%% Reset FSM performance statistics
fsm_reset_stats(FSMPid) when is_pid(FSMPid) ->
    % This could be extended to actually reset stats in the runtime
    ok;
fsm_reset_stats(FSM) ->
    {error, {invalid_fsm_pid, FSM}}.

%% ============================================================================
%% FSM Utilities
%% ============================================================================

%% Check if FSM is alive
fsm_is_alive(FSMPid) when is_pid(FSMPid) ->
    erlang:is_process_alive(FSMPid);
fsm_is_alive(_) ->
    false.

%% Monitor FSM process
fsm_monitor(FSMPid) when is_pid(FSMPid) ->
    MonitorRef = erlang:monitor(process, FSMPid),
    {ok, MonitorRef};
fsm_monitor(FSM) ->
    {error, {invalid_fsm_pid, FSM}}.

%% Link to FSM process
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

%% Unlink from FSM process
fsm_unlink(FSMPid) when is_pid(FSMPid) ->
    try
        erlang:unlink(FSMPid),
        ok
    catch
        error:Reason -> {error, Reason}
    end;
fsm_unlink(FSM) ->
    {error, {invalid_fsm_pid, FSM}}.

%% Set FSM timeout
fsm_set_timeout(FSMPid, Duration, Event) when is_pid(FSMPid), is_integer(Duration) ->
    cure_fsm_runtime:set_timeout(FSMPid, Duration, Event),
    ok;
fsm_set_timeout(FSM, _Duration, _Event) ->
    {error, {invalid_fsm_pid, FSM}}.

%% Clear FSM timeout
fsm_clear_timeout(FSMPid) when is_pid(FSMPid) ->
    cure_fsm_runtime:clear_timeout(FSMPid),
    ok;
fsm_clear_timeout(FSM) ->
    {error, {invalid_fsm_pid, FSM}}.

%% ============================================================================
%% FSM Validation and Introspection
%% ============================================================================

%% Validate FSM type (direct interface)
fsm_validate_type(FSMType) when is_atom(FSMType) ->
    case cure_fsm_runtime:lookup_fsm_definition(FSMType) of
        {ok, _Definition} -> ok;
        {error, not_found} -> {error, {fsm_type_not_found, FSMType}}
    end;
fsm_validate_type(FSMType) ->
    {error, {invalid_fsm_type, FSMType}}.

%% Validate FSM event (direct interface)
fsm_validate_event(FSMPid, Event) when is_pid(FSMPid) ->
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
fsm_validate_event(FSM, _Event) ->
    {error, {invalid_fsm_pid, FSM}}.

%% Get registered FSM types
fsm_get_registered_types() ->
    cure_fsm_runtime:get_registered_fsm_types().

%% Lookup FSM definition
fsm_lookup_definition(FSMType) when is_atom(FSMType) ->
    cure_fsm_runtime:lookup_fsm_definition(FSMType);
fsm_lookup_definition(FSMType) ->
    {error, {invalid_fsm_type, FSMType}}.

%% ============================================================================
%% Legacy Compatibility Functions (for tests)
%% ============================================================================

%% Legacy validate FSM type
validate_fsm_type(FSMType) ->
    fsm_validate_type(FSMType).

%% Legacy validate FSM event
validate_fsm_event(FSMPid, Event) ->
    fsm_validate_event(FSMPid, Event).

%% ============================================================================
%% Internal Helper Functions
%% ============================================================================

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
