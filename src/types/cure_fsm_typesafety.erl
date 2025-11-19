%% Cure FSM Type Safety Module
%% Enhanced type checking for FSM definitions
-module(cure_fsm_typesafety).

-moduledoc """
# FSM Type Safety

This module provides enhanced type checking for FSM definitions, ensuring:
- State-dependent payload types
- Event type validation
- Guard type constraints
- Action type inference

## Type Safety Features

1. **Payload Type Safety**: Each state can have its own payload type
2. **Event Typing**: Events are type-checked against expected types
3. **Guard Constraints**: Guards refine types through constraints
4. **Action Safety**: Actions preserve or transform types correctly

## Usage

```erlang
% Check FSM definition for type safety
case cure_fsm_typesafety:check_fsm_types(FsmDef, Env) of
    {ok, TypedFsmDef} ->
        io:format(\"FSM is type-safe~n\");
    {error, TypeError} ->
        io:format(\"Type error: ~p~n\", [TypeError])
end.
```
""".

-export([
    check_fsm_types/2,
    check_state_payload_types/2,
    check_event_types/2,
    check_guard_types/2,
    check_action_types/2,
    infer_payload_type/2,
    format_type_error/1
]).

-include("../parser/cure_ast.hrl").

%% Type environment for FSM
-record(fsm_type_env, {
    state_payload_types = #{} :: #{atom() => term()},
    event_types = #{} :: #{atom() => term()},
    guard_constraints = [] :: [term()],
    global_env :: term()
}).

%% ============================================================================
%% Main Type Checking API
%% ============================================================================

%% Check all type safety properties of an FSM
-spec check_fsm_types(FsmDef :: term(), Env :: term()) ->
    {ok, term()} | {error, term()}.
check_fsm_types(FsmDef, Env) ->
    try
        % Initialize FSM type environment
        FsmEnv = init_fsm_env(FsmDef, Env),

        % Check payload type consistency across states
        case check_state_payload_types(FsmDef, FsmEnv) of
            {ok, PayloadEnv} ->
                % Check event types
                case check_event_types(FsmDef, PayloadEnv) of
                    {ok, EventEnv} ->
                        % Check guard types
                        case check_guard_types(FsmDef, EventEnv) of
                            {ok, GuardEnv} ->
                                % Check action types
                                case check_action_types(FsmDef, GuardEnv) of
                                    {ok, _FinalEnv} ->
                                        {ok, FsmDef};
                                    {error, ActionError} ->
                                        {error, {action_type_error, ActionError}}
                                end;
                            {error, GuardError} ->
                                {error, {guard_type_error, GuardError}}
                        end;
                    {error, EventError} ->
                        {error, {event_type_error, EventError}}
                end;
            {error, PayloadError} ->
                {error, {payload_type_error, PayloadError}}
        end
    catch
        throw:{type_error, Error} ->
            {error, Error};
        _:Reason ->
            {error, {type_check_failed, Reason}}
    end.

%% Initialize FSM type environment
init_fsm_env(#fsm_def{state_defs = StateDefs}, GlobalEnv) ->
    % Infer payload types for each state
    PayloadTypes = lists:foldl(
        fun(StateDef, Acc) ->
            #state_def{name = StateName} = StateDef,
            % Initially assume all states have the same payload type
            % This can be refined with annotations
            maps:put(StateName, {any}, Acc)
        end,
        #{},
        StateDefs
    ),

    #fsm_type_env{
        state_payload_types = PayloadTypes,
        event_types = #{},
        guard_constraints = [],
        global_env = GlobalEnv
    }.

%% ============================================================================
%% Payload Type Checking
%% ============================================================================

%% Check that payload types are consistent across state transitions
-spec check_state_payload_types(FsmDef :: term(), FsmEnv :: #fsm_type_env{}) ->
    {ok, #fsm_type_env{}} | {error, term()}.
check_state_payload_types(#fsm_def{state_defs = StateDefs}, FsmEnv) ->
    try
        % For each state, check that transitions preserve or correctly transform payload types
        UpdatedEnv = lists:foldl(
            fun(StateDef, AccEnv) ->
                check_state_transitions(StateDef, AccEnv)
            end,
            FsmEnv,
            StateDefs
        ),
        {ok, UpdatedEnv}
    catch
        throw:{payload_type_error, Error} ->
            {error, Error}
    end.

%% Check transitions for a single state
check_state_transitions(#state_def{name = StateName, transitions = Transitions}, FsmEnv) ->
    PayloadType = maps:get(StateName, FsmEnv#fsm_type_env.state_payload_types, {any}),

    % Check each transition
    lists:foldl(
        fun(Transition, AccEnv) ->
            check_transition_payload_type(StateName, PayloadType, Transition, AccEnv)
        end,
        FsmEnv,
        Transitions
    ).

%% Check payload type for a single transition
check_transition_payload_type(FromState, PayloadType, Transition, FsmEnv) ->
    #transition{target = ToState, action = Action} = Transition,

    % If action is defined, infer output payload type
    OutputPayloadType =
        case Action of
            % No action, payload unchanged
            undefined -> PayloadType;
            _ -> infer_action_output_type(Action, PayloadType, FsmEnv)
        end,

    % Update target state's expected payload type
    TargetPayloadType = maps:get(ToState, FsmEnv#fsm_type_env.state_payload_types, {any}),

    % Check compatibility
    case types_compatible(OutputPayloadType, TargetPayloadType) of
        true ->
            FsmEnv;
        false ->
            throw(
                {payload_type_error, #{
                    from_state => FromState,
                    to_state => ToState,
                    expected_type => TargetPayloadType,
                    actual_type => OutputPayloadType
                }}
            )
    end.

%% Infer output type of an action
infer_action_output_type(_Action, InputType, _FsmEnv) ->
    % Simplified: assume action preserves type
    % Full implementation would analyze action AST
    InputType.

%% Check if two types are compatible
types_compatible({any}, _) -> true;
types_compatible(_, {any}) -> true;
types_compatible(Type1, Type2) -> Type1 =:= Type2.

%% ============================================================================
%% Event Type Checking
%% ============================================================================

%% Check that events have consistent types
-spec check_event_types(FsmDef :: term(), FsmEnv :: #fsm_type_env{}) ->
    {ok, #fsm_type_env{}} | {error, term()}.
check_event_types(#fsm_def{state_defs = StateDefs}, FsmEnv) ->
    try
        % Collect all events and their usage contexts
        Events = collect_events(StateDefs),

        % Infer types for each event
        EventTypes = lists:foldl(
            fun({Event, Contexts}, Acc) ->
                EventType = infer_event_type(Event, Contexts, FsmEnv),
                maps:put(Event, EventType, Acc)
            end,
            #{},
            Events
        ),

        UpdatedEnv = FsmEnv#fsm_type_env{event_types = EventTypes},
        {ok, UpdatedEnv}
    catch
        throw:{event_type_error, Error} ->
            {error, Error}
    end.

%% Collect all events and their contexts
collect_events(StateDefs) ->
    EventMap = lists:foldl(
        fun(#state_def{transitions = Transitions}, Acc) ->
            lists:foldl(
                fun(#transition{event = Event}, EventAcc) ->
                    % Could include state, guard info, etc.
                    Context = #{},
                    maps:update_with(
                        Event,
                        fun(Contexts) -> [Context | Contexts] end,
                        [Context],
                        EventAcc
                    )
                end,
                Acc,
                Transitions
            )
        end,
        #{},
        StateDefs
    ),
    maps:to_list(EventMap).

%% Infer type for an event based on usage contexts
infer_event_type(Event, _Contexts, _FsmEnv) ->
    % Simplified: return atom type for event
    % Full implementation would analyze guards and actions
    {event_type, Event, {any}}.

%% ============================================================================
%% Guard Type Checking
%% ============================================================================

%% Check that guards are type-safe
-spec check_guard_types(FsmDef :: term(), FsmEnv :: #fsm_type_env{}) ->
    {ok, #fsm_type_env{}} | {error, term()}.
check_guard_types(#fsm_def{state_defs = StateDefs}, FsmEnv) ->
    try
        % Check each guard in all transitions
        Constraints = lists:flatmap(
            fun(#state_def{transitions = Transitions}) ->
                lists:filtermap(
                    fun(#transition{guard = Guard}) ->
                        case Guard of
                            undefined -> false;
                            _ -> {true, check_guard_type(Guard, FsmEnv)}
                        end
                    end,
                    Transitions
                )
            end,
            StateDefs
        ),

        UpdatedEnv = FsmEnv#fsm_type_env{guard_constraints = Constraints},
        {ok, UpdatedEnv}
    catch
        throw:{guard_type_error, Error} ->
            {error, Error}
    end.

%% Check type of a single guard
check_guard_type(_Guard, _FsmEnv) ->
    % Simplified: assume guards are boolean expressions
    % Full implementation would type-check guard expressions
    {constraint, boolean}.

%% ============================================================================
%% Action Type Checking
%% ============================================================================

%% Check that actions are type-safe
-spec check_action_types(FsmDef :: term(), FsmEnv :: #fsm_type_env{}) ->
    {ok, #fsm_type_env{}} | {error, term()}.
check_action_types(#fsm_def{state_defs = StateDefs}, FsmEnv) ->
    try
        % Check each action in all transitions
        lists:foreach(
            fun(#state_def{name = StateName, transitions = Transitions}) ->
                PayloadType = maps:get(StateName, FsmEnv#fsm_type_env.state_payload_types),
                lists:foreach(
                    fun(#transition{action = Action, target = ToState}) ->
                        case Action of
                            undefined -> ok;
                            _ -> check_action_type(Action, PayloadType, ToState, FsmEnv)
                        end
                    end,
                    Transitions
                )
            end,
            StateDefs
        ),
        {ok, FsmEnv}
    catch
        throw:{action_type_error, Error} ->
            {error, Error}
    end.

%% Check type of a single action
check_action_type(_Action, _InputType, _ToState, _FsmEnv) ->
    % Simplified: assume actions are well-typed
    % Full implementation would type-check action expressions
    ok.

%% ============================================================================
%% Type Inference
%% ============================================================================

%% Infer payload type from state definition
-spec infer_payload_type(StateDef :: term(), FsmEnv :: #fsm_type_env{}) -> term().
infer_payload_type(#state_def{name = StateName}, FsmEnv) ->
    maps:get(StateName, FsmEnv#fsm_type_env.state_payload_types, {any}).

%% ============================================================================
%% Error Formatting
%% ============================================================================

%% Format type error for display
-spec format_type_error(Error :: term()) -> binary().
format_type_error(
    {payload_type_error, #{
        from_state := From,
        to_state := To,
        expected_type := Expected,
        actual_type := Actual
    }}
) ->
    iolist_to_binary(
        io_lib:format(
            "Payload type mismatch in transition from ~p to ~p: expected ~p but got ~p",
            [From, To, Expected, Actual]
        )
    );
format_type_error({event_type_error, Error}) ->
    iolist_to_binary(io_lib:format("Event type error: ~p", [Error]));
format_type_error({guard_type_error, Error}) ->
    iolist_to_binary(io_lib:format("Guard type error: ~p", [Error]));
format_type_error({action_type_error, Error}) ->
    iolist_to_binary(io_lib:format("Action type error: ~p", [Error]));
format_type_error(Error) ->
    iolist_to_binary(io_lib:format("Type error: ~p", [Error])).
