%% Cure Programming Language - FSM Cure API Wrapper
%% Provides the Cure-level FSM API that wraps cure_fsm_runtime gen_server
-module(cure_fsm_cure_api).

-moduledoc """
# Cure FSM API Wrapper

This module provides the Cure-level FSM API that matches the design in lib/std/fsm.cure.
It wraps the underlying cure_fsm_runtime gen_server to provide:

- start_fsm/1: Start an FSM instance from a module
- fsm_cast/2: Send events asynchronously  
- fsm_advertise/2: Register a name for an FSM
- fsm_state/1: Query current state and payload

The FSM definitions in Cure modules are compiled to:
1. A record type for the payload
2. A list of transitions with handler functions
3. An initial state and initial payload

This module bridges the gap between Cure's high-level FSM syntax and the
Erlang gen_server runtime.
""".

-export([
    start_fsm/1,
    fsm_cast/2,
    fsm_advertise/2,
    fsm_state/1
]).

-include("../parser/cure_ast.hrl").
-include("cure_fsm_runtime.hrl").

%% @doc Start an FSM instance from a Cure module
%%
%% The module must have been compiled with an FSM definition that includes:
%% - A payload record type
%% - Initial state and payload
%% - Transition handlers
%%
%% Args:
%%   Module - Atom representing the Cure module name (e.g. 'Elixir.Turnstile')
%%
%% Returns:
%%   {ok, Pid} - FSM process PID
%%   {error, Reason} - Error starting FSM
-spec start_fsm(Module :: atom()) -> {ok, pid()} | {error, term()}.
start_fsm(Module) when is_atom(Module) ->
    % Look up the compiled FSM definition from the module
    case get_module_fsm_definition(Module) of
        {ok, FsmDef} ->
            % Extract initial state and payload from the FSM definition
            #fsm_definition{
                name = FsmName,
                initial_state = InitialState,
                initial_payload = InitialPayload
            } = FsmDef,

            % Start the FSM using the runtime
            case cure_fsm_runtime:start_fsm(FsmName, InitialPayload) of
                {ok, Pid} ->
                    {ok, Pid};
                Error ->
                    Error
            end;
        {error, Reason} ->
            {error, {fsm_definition_not_found, Module, Reason}}
    end.

%% @doc Send an event asynchronously to an FSM
%%
%% Args:
%%   Target - Either a Pid or a registered name (atom)
%%   Event - A tuple {EventName, EventPayload} where:
%%           EventName is an atom
%%           EventPayload is a list of {key, value} pairs
%%
%% Returns:
%%   ok - Event sent (asynchronous, no guarantee of processing)
-spec fsm_cast(Target :: pid() | atom(), Event :: {atom(), list()}) -> ok.
fsm_cast(Target, {EventName, EventPayload}) when is_atom(EventName), is_list(EventPayload) ->
    % Resolve target to PID if it's a name
    TargetPid =
        case Target of
            Pid when is_pid(Pid) -> Pid;
            Name when is_atom(Name) ->
                case whereis(Name) of
                    undefined ->
                        error({fsm_not_found, Name});
                    Pid ->
                        Pid
                end
        end,

    % Send the event to the FSM runtime
    % The runtime will look up the appropriate handler and invoke it
    cure_fsm_runtime:send_event(TargetPid, EventName, EventPayload),
    ok.

%% @doc Register a name for an FSM process
%%
%% Args:
%%   Pid - FSM process PID
%%   Name - Atom to register as the FSM name
%%
%% Returns:
%%   ok - Name registered
%%   {error, Reason} - Registration failed
-spec fsm_advertise(Pid :: pid(), Name :: atom()) -> ok | {error, term()}.
fsm_advertise(Pid, Name) when is_pid(Pid), is_atom(Name) ->
    try
        register(Name, Pid),
        ok
    catch
        error:badarg ->
            {error, {name_already_registered, Name}};
        error:Reason ->
            {error, Reason}
    end.

%% @doc Query the current state and payload of an FSM
%%
%% Args:
%%   Target - Either a Pid or a registered name (atom)
%%
%% Returns:
%%   {ok, {StateName, Payload}} - Current state and payload
%%   {error, Reason} - Error querying state
-spec fsm_state(Target :: pid() | atom()) -> {ok, {atom(), term()}} | {error, term()}.
fsm_state(Target) ->
    % Resolve target to PID if it's a name
    TargetPid =
        case Target of
            Pid when is_pid(Pid) -> Pid;
            Name when is_atom(Name) ->
                case whereis(Name) of
                    undefined ->
                        error({fsm_not_found, Name});
                    Pid ->
                        Pid
                end
        end,

    % Query the FSM runtime for current state
    case cure_fsm_runtime:get_fsm_info(TargetPid) of
        {ok, #{current_state := StateName, data := Payload}} ->
            {ok, {StateName, Payload}};
        {ok, #{current_state := StateName}} ->
            {ok, {StateName, undefined}};
        Error ->
            Error
    end.

%% ============================================================================
%% Internal Helper Functions
%% ============================================================================

%% Get the FSM definition from a compiled Cure module
%%
%% This looks for the module's __fsm_definition__/0 function which is
%% generated by the Cure compiler when compiling an FSM definition.
-spec get_module_fsm_definition(Module :: atom()) -> {ok, #fsm_definition{}} | {error, term()}.
get_module_fsm_definition(Module) ->
    try
        % Try to call Module:'__fsm_definition__'()
        case erlang:function_exported(Module, '__fsm_definition__', 0) of
            true ->
                FsmDef = Module:'__fsm_definition__'(),
                {ok, FsmDef};
            false ->
                {error, no_fsm_definition_exported}
        end
    catch
        error:undef ->
            {error, {module_not_loaded, Module}};
        Error:Reason ->
            {error, {Error, Reason}}
    end.
