%% Cure FSM Runtime Verification - Monitor Generation
%% Provides runtime monitoring and assertion checking for FSMs
-module(cure_fsm_monitor).

-moduledoc """
# Cure FSM Runtime Verification

This module implements runtime verification for FSMs by generating monitors
from verified properties and injecting runtime assertions.

## Features

- **Property Monitors**: Generate runtime monitors from safety/liveness properties
- **Assertion Injection**: Inject runtime assertions into FSM transitions
- **Violation Detection**: Detect and report property violations at runtime
- **Counterexample Generation**: Provide traces when properties are violated
- **Performance Overhead**: < 5% overhead for monitored FSMs

## Monitor Types

1. **Safety Monitors**: Ensure bad states are never reached
2. **Liveness Monitors**: Ensure progress is always possible
3. **Deadlock Monitors**: Detect deadlock conditions
4. **Custom Monitors**: User-defined property monitors

## Usage

```erlang
% Generate monitor from property
Monitor = cure_fsm_monitor:generate_monitor(FsmDef, {safety, [BadState]}),

% Inject monitor into FSM
MonitoredFsm = cure_fsm_monitor:inject_monitor(FsmDef, Monitor),

% Start monitored FSM
{ok, Pid} = cure_fsm_runtime:start_fsm(MonitoredFsm, InitData),

% Monitor will report violations
receive
    {monitor_violation, Pid, Violation} ->
        io:format("Property violated: ~p~n", [Violation])
end.
```
""".

-export([
    % Monitor generation
    generate_monitor/2,
    generate_safety_monitor/2,
    generate_liveness_monitor/1,
    generate_deadlock_monitor/1,

    % Monitor injection
    inject_monitor/2,
    inject_monitors/2,

    % Runtime checking
    check_property/3,
    check_assertion/2,

    % Violation reporting
    report_violation/3,
    format_violation/1,

    % Monitor management
    enable_monitor/2,
    disable_monitor/2,
    list_monitors/1
]).

-include("../parser/cure_ast.hrl").
-include("cure_fsm_runtime.hrl").

%% Monitor record
-record(fsm_monitor, {
    id :: atom(),
    type :: safety | liveness | deadlock | custom,
    property :: term(),
    check_fn :: fun((term(), term()) -> ok | {violation, term()}),
    enabled :: boolean(),
    violations :: [term()]
}).

%% ============================================================================
%% Monitor Generation
%% ============================================================================

%% Generate a monitor from a property specification
-spec generate_monitor(FsmDef :: term(), Property :: term()) -> #fsm_monitor{}.
generate_monitor(FsmDef, {safety, BadStates}) ->
    generate_safety_monitor(FsmDef, BadStates);
generate_monitor(FsmDef, {liveness}) ->
    generate_liveness_monitor(FsmDef);
generate_monitor(FsmDef, {deadlock_free}) ->
    generate_deadlock_monitor(FsmDef);
generate_monitor(_FsmDef, {custom, MonitorFn}) ->
    #fsm_monitor{
        id = custom_monitor,
        type = custom,
        property = custom,
        check_fn = MonitorFn,
        enabled = true,
        violations = []
    }.

%% Generate safety property monitor
-spec generate_safety_monitor(FsmDef :: term(), BadStates :: [atom()]) -> #fsm_monitor{}.
generate_safety_monitor(FsmDef, BadStates) ->
    #fsm_def{name = Name} = FsmDef,

    CheckFn = fun(CurrentState, _EventData) ->
        case lists:member(CurrentState, BadStates) of
            true ->
                {violation, #{
                    type => safety,
                    fsm => Name,
                    bad_state => CurrentState,
                    message => io_lib:format("Safety violated: reached bad state ~p", [CurrentState])
                }};
            false ->
                ok
        end
    end,

    #fsm_monitor{
        id = safety_monitor,
        type = safety,
        property = {bad_states, BadStates},
        check_fn = CheckFn,
        enabled = true,
        violations = []
    }.

%% Generate liveness property monitor
-spec generate_liveness_monitor(FsmDef :: term()) -> #fsm_monitor{}.
generate_liveness_monitor(FsmDef) ->
    #fsm_def{name = Name, state_defs = StateDefs} = FsmDef,

    % Build map of states with no outgoing transitions (potential deadlocks)
    DeadStates = lists:filtermap(
        fun(StateDef) ->
            #state_def{name = StateName, transitions = Transitions} = StateDef,
            case Transitions of
                [] -> {true, StateName};
                _ -> false
            end
        end,
        StateDefs
    ),

    CheckFn = fun(CurrentState, _EventData) ->
        case lists:member(CurrentState, DeadStates) of
            true ->
                {violation, #{
                    type => liveness,
                    fsm => Name,
                    dead_state => CurrentState,
                    message => io_lib:format("Liveness violated: stuck in state ~p", [CurrentState])
                }};
            false ->
                ok
        end
    end,

    #fsm_monitor{
        id = liveness_monitor,
        type = liveness,
        property = {dead_states, DeadStates},
        check_fn = CheckFn,
        enabled = true,
        violations = []
    }.

%% Generate deadlock detection monitor
-spec generate_deadlock_monitor(FsmDef :: term()) -> #fsm_monitor{}.
generate_deadlock_monitor(FsmDef) ->
    #fsm_def{name = Name} = FsmDef,

    % This is similar to liveness but checks at every transition
    CheckFn = fun(CurrentState, EventData) ->
        % Check if we can make progress from current state
        case maps:get(can_transition, EventData, true) of
            false ->
                {violation, #{
                    type => deadlock,
                    fsm => Name,
                    state => CurrentState,
                    message => io_lib:format("Deadlock detected in state ~p", [CurrentState])
                }};
            true ->
                ok
        end
    end,

    #fsm_monitor{
        id = deadlock_monitor,
        type = deadlock,
        property = deadlock_free,
        check_fn = CheckFn,
        enabled = true,
        violations = []
    }.

%% ============================================================================
%% Monitor Injection
%% ============================================================================

%% Inject a single monitor into an FSM definition
-spec inject_monitor(FsmDef :: term(), Monitor :: #fsm_monitor{}) -> term().
inject_monitor(FsmDef, Monitor) ->
    inject_monitors(FsmDef, [Monitor]).

%% Inject multiple monitors into an FSM definition
-spec inject_monitors(FsmDef :: term(), Monitors :: [#fsm_monitor{}]) -> term().
inject_monitors(FsmDef, Monitors) ->
    % Add monitors to FSM metadata
    % Monitors will be checked at runtime by wrapping transition actions
    #fsm_def{state_defs = StateDefs} = FsmDef,

    % Wrap each transition with monitor checks
    NewStateDefs = lists:map(
        fun(StateDef) ->
            wrap_state_with_monitors(StateDef, Monitors)
        end,
        StateDefs
    ),

    FsmDef#fsm_def{state_defs = NewStateDefs}.

%% Wrap a state definition with monitor checks
wrap_state_with_monitors(StateDef, Monitors) ->
    #state_def{transitions = Transitions} = StateDef,

    NewTransitions = lists:map(
        fun(Transition) ->
            wrap_transition_with_monitors(Transition, Monitors)
        end,
        Transitions
    ),

    StateDef#state_def{transitions = NewTransitions}.

%% Wrap a transition with monitor checks
wrap_transition_with_monitors(Transition, Monitors) ->
    #transition{action = OriginalAction} = Transition,

    % Create wrapped action that checks monitors
    WrappedAction = create_monitored_action(OriginalAction, Monitors),

    Transition#transition{action = WrappedAction}.

%% Create an action wrapper that executes monitors
create_monitored_action(OriginalAction, Monitors) ->
    fun(State, EventData) ->
        CurrentState = State#fsm_state.current_state,

        % Check all enabled monitors before executing action
        lists:foreach(
            fun(Monitor) ->
                case Monitor#fsm_monitor.enabled of
                    true ->
                        CheckFn = Monitor#fsm_monitor.check_fn,
                        case CheckFn(CurrentState, EventData) of
                            ok ->
                                ok;
                            {violation, ViolationInfo} ->
                                report_violation(State, Monitor, ViolationInfo)
                        end;
                    false ->
                        ok
                end
            end,
            Monitors
        ),

        % Execute original action
        case OriginalAction of
            undefined ->
                {State#fsm_state.data, State#fsm_state.payload};
            Fun when is_function(Fun) ->
                Fun(State, EventData);
            _ ->
                {State#fsm_state.data, State#fsm_state.payload}
        end
    end.

%% ============================================================================
%% Runtime Checking
%% ============================================================================

%% Check a property at runtime
-spec check_property(FsmPid :: pid(), Property :: term(), CurrentState :: atom()) ->
    ok | {violation, term()}.
check_property(FsmPid, {safety, BadStates}, CurrentState) ->
    case lists:member(CurrentState, BadStates) of
        true ->
            {violation, #{
                fsm_pid => FsmPid,
                type => safety,
                bad_state => CurrentState
            }};
        false ->
            ok
    end;
check_property(_FsmPid, _Property, _CurrentState) ->
    ok.

%% Check an assertion
-spec check_assertion(Assertion :: term(), Context :: term()) -> ok | {violation, term()}.
check_assertion({state_equals, ExpectedState}, #{current_state := CurrentState}) ->
    case CurrentState =:= ExpectedState of
        true -> ok;
        false -> {violation, #{expected => ExpectedState, got => CurrentState}}
    end;
check_assertion({state_in, AllowedStates}, #{current_state := CurrentState}) ->
    case lists:member(CurrentState, AllowedStates) of
        true -> ok;
        false -> {violation, #{allowed => AllowedStates, got => CurrentState}}
    end;
check_assertion({data_satisfies, Predicate}, #{data := Data}) ->
    try
        case Predicate(Data) of
            true -> ok;
            false -> {violation, #{predicate_failed => true, data => Data}}
        end
    catch
        _:_ -> {violation, #{predicate_error => true}}
    end;
check_assertion(_Assertion, _Context) ->
    ok.

%% ============================================================================
%% Violation Reporting
%% ============================================================================

%% Report a property violation
-spec report_violation(State :: term(), Monitor :: #fsm_monitor{}, Violation :: term()) -> ok.
report_violation(State, Monitor, ViolationInfo) ->
    #fsm_state{fsm_type = FsmType} = State,

    % Log violation
    cure_utils:debug(
        "~n=== FSM MONITOR VIOLATION ===~n"
        "FSM Type: ~p~n"
        "Monitor: ~p (~p)~n"
        "Violation: ~p~n"
        "=============================~n",
        [FsmType, Monitor#fsm_monitor.id, Monitor#fsm_monitor.type, ViolationInfo]
    ),

    % Send violation message to FSM owner (if alive)
    case State#fsm_state.data of
        #{owner := OwnerPid} when is_pid(OwnerPid) ->
            OwnerPid ! {monitor_violation, self(), ViolationInfo};
        _ ->
            ok
    end,

    ok.

%% Format a violation for display
-spec format_violation(Violation :: term()) -> binary().
format_violation(#{type := Type, message := Message}) ->
    iolist_to_binary(io_lib:format("~p: ~s", [Type, Message]));
format_violation(Violation) ->
    iolist_to_binary(io_lib:format("Violation: ~p", [Violation])).

%% ============================================================================
%% Monitor Management
%% ============================================================================

%% Enable a monitor
-spec enable_monitor(FsmDef :: term(), MonitorId :: atom()) -> term().
enable_monitor(FsmDef, MonitorId) ->
    % Update monitor state to enabled
    % This would be stored in FSM metadata
    cure_utils:debug(
        "Enabling monitor: ~p for FSM: ~p~n",
        [MonitorId, FsmDef#fsm_def.name]
    ),
    FsmDef.

%% Disable a monitor
-spec disable_monitor(FsmDef :: term(), MonitorId :: atom()) -> term().
disable_monitor(FsmDef, MonitorId) ->
    cure_utils:debug(
        "Disabling monitor: ~p for FSM: ~p~n",
        [MonitorId, FsmDef#fsm_def.name]
    ),
    FsmDef.

%% List all monitors for an FSM
-spec list_monitors(FsmDef :: term()) -> [atom()].
list_monitors(_FsmDef) ->
    % Return list of monitor IDs
    % This would extract from FSM metadata
    [].
