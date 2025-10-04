%% Cure Programming Language - FSM Runtime System
%% Optimized runtime for finite state machine execution on BEAM VM
-module(cure_fsm_runtime).

%% Public API
-export([
    % FSM lifecycle
    start_fsm/2, start_fsm/3,
    stop_fsm/1,
    
    % FSM operations
    send_event/2, send_event/3,
    get_state/1,
    get_fsm_info/1,
    
    % FSM registration and compilation
    register_fsm_type/2,
    get_registered_fsm_types/0,
    unregister_fsm_type/1,
    lookup_fsm_definition/1,
    clear_fsm_registry/0,
    compile_fsm_definition/1,
    
    % Performance optimizations
    send_batch_events/2,
    get_performance_stats/1,
    
    % Timeout handling
    set_timeout/3,
    clear_timeout/1
]).

%% Internal gen_server API (for FSM processes)
-export([
    init/1,
    handle_call/3,
    handle_cast/2,
    handle_info/2,
    terminate/2,
    code_change/3
]).

-behaviour(gen_server).

%% Include AST definitions and FSM records
-include("../parser/cure_ast_simple.hrl").
-include("cure_fsm_runtime.hrl").

%% Global FSM definition registry
-define(FSM_REGISTRY, cure_fsm_registry).

%% ============================================================================
%% Public API
%% ============================================================================

%% Start a new FSM instance
start_fsm(FSMType, InitialData) ->
    start_fsm(FSMType, InitialData, []).

start_fsm(FSMType, InitialData, Options) ->
    case lookup_fsm_definition(FSMType) of
        {ok, Definition} ->
            gen_server:start_link(?MODULE, {FSMType, Definition, InitialData, Options}, []);
        {error, not_found} ->
            {error, {fsm_type_not_found, FSMType}}
    end.

%% Stop an FSM instance
stop_fsm(FSMPid) when is_pid(FSMPid) ->
    gen_server:call(FSMPid, stop).

%% Send an event to an FSM
send_event(FSMPid, Event) ->
    send_event(FSMPid, Event, undefined).

send_event(FSMPid, Event, Data) when is_pid(FSMPid) ->
    gen_server:cast(FSMPid, {event, Event, Data}).

%% Get current state of an FSM
get_state(FSMPid) when is_pid(FSMPid) ->
    gen_server:call(FSMPid, get_state).

%% Get FSM information (for debugging)
get_fsm_info(FSMPid) when is_pid(FSMPid) ->
    gen_server:call(FSMPid, get_fsm_info).

%% Set a timeout for the current state
set_timeout(FSMPid, Timeout, Event) when is_pid(FSMPid) ->
    gen_server:cast(FSMPid, {set_timeout, Timeout, Event}).

%% Clear any existing timeout
clear_timeout(FSMPid) when is_pid(FSMPid) ->
    gen_server:cast(FSMPid, clear_timeout).

%% Send batch events for better performance
send_batch_events(FSMPid, Events) when is_pid(FSMPid), is_list(Events) ->
    gen_server:cast(FSMPid, {batch_events, Events}).

%% Get performance statistics
get_performance_stats(FSMPid) when is_pid(FSMPid) ->
    gen_server:call(FSMPid, get_perf_stats).

%% ============================================================================
%% Registry Functions
%% ============================================================================

%% Initialize FSM registry
init_fsm_registry() ->
    case ets:info(?FSM_REGISTRY) of
        undefined ->
            ets:new(?FSM_REGISTRY, [named_table, public, set]),
            ok;
        _ -> ok
    end.

%% Register a new FSM type
register_fsm_type(FSMType, Definition) when is_atom(FSMType) ->
    init_fsm_registry(),
    ets:insert(?FSM_REGISTRY, {FSMType, Definition}),
    ok.

%% Get all registered FSM types
get_registered_fsm_types() ->
    init_fsm_registry(),
    [FSMType || {FSMType, _} <- ets:tab2list(?FSM_REGISTRY)].

%% Unregister an FSM type
unregister_fsm_type(FSMType) when is_atom(FSMType) ->
    init_fsm_registry(),
    ets:delete(?FSM_REGISTRY, FSMType).

%% Clear the FSM registry
clear_fsm_registry() ->
    case ets:info(?FSM_REGISTRY) of
        undefined -> ok;
        _ -> 
            ets:delete_all_objects(?FSM_REGISTRY),
            ok
    end.

%% Lookup an FSM definition
lookup_fsm_definition(FSMType) ->
    init_fsm_registry(),
    case ets:lookup(?FSM_REGISTRY, FSMType) of
        [{FSMType, Definition}] -> {ok, Definition};
        [] -> {error, not_found}
    end.

%% ============================================================================
%% gen_server callbacks
%% ============================================================================

init({FSMType, Definition, InitialData, _Options}) ->
    #fsm_definition{
        initial_state = InitialState,
        transitions = Transitions,
        timeouts = Timeouts
    } = Definition,
    
    State = #fsm_state{
        fsm_type = FSMType,
        current_state = InitialState,
        data = InitialData,
        event_data = undefined,
        timeout_ref = undefined,
        transitions = Transitions,
        timeouts = Timeouts,
        event_history = [],
        perf_stats = #fsm_perf_stats{
            events_processed = 0,
            avg_event_time = 0.0,
            max_event_time = 0.0,
            memory_usage = 0,
            last_updated = erlang:monotonic_time(microsecond)
        }
    },
    
    % Set initial timeout if defined for the initial state
    NewState = maybe_set_state_timeout(State),
    
    {ok, NewState}.

handle_call(stop, _From, State) ->
    {stop, normal, ok, State};

handle_call(get_state, _From, #fsm_state{current_state = CurrentState} = State) ->
    {reply, {ok, CurrentState}, State};

handle_call(get_fsm_info, _From, State) ->
    #fsm_state{
        fsm_type = FSMType,
        current_state = CurrentState,
        data = Data,
        event_history = History
    } = State,
    
    Info = #{
        fsm_type => FSMType,
        current_state => CurrentState,
        data => Data,
        event_history => lists:reverse(History)
    },
    
    {reply, {ok, Info}, State};

handle_call(get_perf_stats, _From, #fsm_state{perf_stats = Stats} = State) ->
    {reply, {ok, Stats}, State};

handle_call(Request, _From, State) ->
    {reply, {error, {unknown_call, Request}}, State}.

handle_cast({event, Event, EventData}, State) ->
    StartTime = erlang:monotonic_time(microsecond),
    NewState = handle_fsm_event(Event, EventData, State),
    FinalState = update_perf_stats(StartTime, NewState),
    {noreply, FinalState};

%% Batch event processing for better performance
handle_cast({batch_events, Events}, State) ->
    StartTime = erlang:monotonic_time(microsecond),
    NewState = handle_batch_events(Events, State),
    FinalState = update_perf_stats(StartTime, NewState),
    {noreply, FinalState};

handle_cast({set_timeout, Timeout, TimeoutEvent}, State) ->
    NewState = set_fsm_timeout(Timeout, TimeoutEvent, State),
    {noreply, NewState};

handle_cast(clear_timeout, State) ->
    NewState = clear_fsm_timeout(State),
    {noreply, NewState};

handle_cast(_Msg, State) ->
    {noreply, State}.

handle_info({timeout, TimerRef, timeout_event}, 
            #fsm_state{timeout_ref = TimerRef} = State) ->
    % Handle timeout event
    StartTime = erlang:monotonic_time(microsecond),
    NewState = handle_fsm_event(timeout, undefined, State),
    FinalState = update_perf_stats(StartTime, NewState#fsm_state{timeout_ref = undefined}),
    {noreply, FinalState};

handle_info(_Info, State) ->
    {noreply, State}.

terminate(_Reason, #fsm_state{timeout_ref = TimerRef}) ->
    case TimerRef of
        undefined -> ok;
        Ref -> erlang:cancel_timer(Ref)
    end,
    ok.

code_change(_OldVsn, State, _Extra) ->
    {ok, State}.

%% ============================================================================
%% Internal FSM Event Handling
%% ============================================================================

%% Handle an FSM event and perform state transition
handle_fsm_event(Event, EventData, State) ->
    #fsm_state{
        current_state = CurrentState,
        transitions = Transitions,
        event_history = History
    } = State,
    
    case find_transition(CurrentState, Event, Transitions) of
        {ok, {TargetState, Guard, Action}} ->
            % Check guard condition
            case evaluate_guard(Guard, State, EventData) of
                true ->
                    % Execute action and transition to new state
                    NewData = execute_action(Action, State, EventData),
                    NewState = State#fsm_state{
                        current_state = TargetState,
                        data = NewData,
                        event_data = EventData,
                        event_history = [{Event, CurrentState, TargetState, erlang:timestamp()} | History]
                    },
                    
                    % Clear old timeout and set new one if needed
                    TransitionedState = clear_fsm_timeout(NewState),
                    OptimizedState = optimize_fsm_state(maybe_set_state_timeout(TransitionedState)),
                    OptimizedState;
                
                false ->
                    % Guard failed, stay in current state
                    State#fsm_state{
                        event_history = [{Event, CurrentState, CurrentState, erlang:timestamp()} | History]
                    }
            end;
        
        {error, no_transition} ->
            % No transition found for this event, stay in current state
            State#fsm_state{
                event_history = [{Event, CurrentState, CurrentState, erlang:timestamp()} | History]
            }
    end.

%% Find a transition for the given state and event (optimized version)
find_transition(State, Event, Transitions) ->
    % Try flat map lookup first (O(1))
    FlatKey = {State, Event},
    case maps:find(FlatKey, Transitions) of
        {ok, Transition} -> 
            {ok, Transition};
        error ->
            % Fallback to nested map lookup for compatibility
            case maps:find(State, Transitions) of
                {ok, StateTransitions} ->
                    case maps:find(Event, StateTransitions) of
                        {ok, Transition} -> {ok, Transition};
                        error -> {error, no_transition}
                    end;
                error -> 
                    {error, no_transition}
            end
    end.

%% Evaluate guard condition (simplified - can be extended)
evaluate_guard(undefined, _State, _EventData) ->
    true;
evaluate_guard(Guard, State, EventData) when is_function(Guard, 2) ->
    try
        Guard(State, EventData)
    catch
        _:_ -> false
    end;
evaluate_guard(_Guard, _State, _EventData) ->
    % TODO: Implement guard expression evaluation
    true.

%% Execute action (simplified - can be extended)
execute_action(undefined, State, _EventData) ->
    State#fsm_state.data;
execute_action(Action, State, EventData) when is_function(Action, 2) ->
    try
        Action(State, EventData)
    catch
        _:_ -> State#fsm_state.data
    end;
execute_action(_Action, State, _EventData) ->
    % TODO: Implement action expression execution
    State#fsm_state.data.

%% Set FSM timeout
set_fsm_timeout(Timeout, _TimeoutEvent, State) ->
    TimerRef = erlang:send_after(Timeout, self(), {timeout, make_ref(), timeout_event}),
    State#fsm_state{timeout_ref = TimerRef}.

%% Clear FSM timeout
clear_fsm_timeout(#fsm_state{timeout_ref = undefined} = State) ->
    State;
clear_fsm_timeout(#fsm_state{timeout_ref = TimerRef} = State) ->
    erlang:cancel_timer(TimerRef),
    State#fsm_state{timeout_ref = undefined}.

%% Set timeout based on state definition
maybe_set_state_timeout(State) ->
    #fsm_state{
        current_state = CurrentState,
        timeouts = Timeouts
    } = State,
    
    case maps:find(CurrentState, Timeouts) of
        {ok, {Timeout, TimeoutEvent}} ->
            set_fsm_timeout(Timeout, TimeoutEvent, State);
        error ->
            State
    end.

%% ============================================================================
%% Performance Optimizations
%% ============================================================================

%% Handle multiple events in batch for reduced message passing overhead
handle_batch_events([], State) ->
    State;
handle_batch_events([{Event, EventData} | Rest], State) ->
    NewState = handle_fsm_event(Event, EventData, State),
    handle_batch_events(Rest, NewState);
handle_batch_events([Event | Rest], State) ->
    NewState = handle_fsm_event(Event, undefined, State),
    handle_batch_events(Rest, NewState).

%% Optimize FSM state by trimming history when it gets too large
optimize_fsm_state(#fsm_state{event_history = History} = State) when length(History) > 100 ->
    % Keep only the last 50 events to prevent unbounded memory growth
    TrimmedHistory = lists:sublist(History, 50),
    State#fsm_state{event_history = TrimmedHistory};
optimize_fsm_state(State) ->
    State.

%% Update performance statistics
update_perf_stats(StartTime, State) ->
    case State#fsm_state.perf_stats of
        undefined -> State;
        PerfStats ->
            EndTime = erlang:monotonic_time(microsecond),
            EventTime = EndTime - StartTime,
            Count = PerfStats#fsm_perf_stats.events_processed,
            OldAvg = PerfStats#fsm_perf_stats.avg_event_time,
            MaxTime = max(EventTime, PerfStats#fsm_perf_stats.max_event_time),
            
            NewAvg = update_avg_time(OldAvg, Count, EventTime),
            NewPerfStats = PerfStats#fsm_perf_stats{
                events_processed = Count + 1,
                avg_event_time = NewAvg,
                max_event_time = MaxTime,
                last_updated = EndTime
            },
            
            State#fsm_state{perf_stats = NewPerfStats}
    end.

%% Update running average
update_avg_time(OldAvg, Count, NewTime) when Count > 0 ->
    (OldAvg * Count + NewTime) / (Count + 1);
update_avg_time(_, 0, NewTime) ->
    float(NewTime).

%% ============================================================================
%% FSM Definition Compilation
%% ============================================================================

%% Compile FSM definition from AST to runtime format
compile_fsm_definition(FSMDef) ->
    #fsm_def{
        name = Name,
        states = States,
        initial = InitialState,
        state_defs = StateDefs
    } = FSMDef,
    
    Transitions = compile_transitions(StateDefs),
    Timeouts = compile_timeouts(StateDefs),
    
    #fsm_definition{
        name = Name,
        states = States,
        initial_state = InitialState,
        transitions = Transitions,
        timeouts = Timeouts
    }.

%% Compile transitions into optimized lookup table
compile_transitions(StateDefs) ->
    % Create both flat and nested maps for optimal lookup performance
    FlatTransitions = lists:foldl(fun(StateDef, Acc) ->
        #state_def{name = StateName, transitions = Transitions} = StateDef,
        StateTransitions = compile_state_transitions(Transitions),
        
        % Add flat entries for O(1) lookup
        FlatEntries = maps:fold(fun(Event, Transition, FlatAcc) ->
            maps:put({StateName, Event}, Transition, FlatAcc)
        end, Acc, StateTransitions),
        
        FlatEntries
    end, #{}, StateDefs),
    
    FlatTransitions.

%% Compile transitions for a single state
compile_state_transitions(Transitions) ->
    lists:foldl(fun(Transition, Acc) ->
        #transition{event = Event, target = Target, guard = Guard, action = Action} = Transition,
        CompiledEvent = extract_event(Event),
        CompiledGuard = compile_guard(Guard),
        CompiledAction = compile_action(Action),
        maps:put(CompiledEvent, {Target, CompiledGuard, CompiledAction}, Acc)
    end, #{}, Transitions).

%% Compile timeouts from state definitions
compile_timeouts(StateDefs) ->
    lists:foldl(fun(StateDef, Acc) ->
        #state_def{name = StateName, transitions = Transitions} = StateDef,
        case find_timeout_in_transitions(Transitions) of
            {ok, {Timeout, Event}} ->
                maps:put(StateName, {Timeout, Event}, Acc);
            not_found ->
                Acc
        end
    end, #{}, StateDefs).

%% Extract event from AST
extract_event({atom, Event}) -> Event;
extract_event(Event) when is_atom(Event) -> Event;
extract_event(_) -> unknown_event.

%% Compile guard expression (placeholder)
compile_guard(undefined) -> undefined;
compile_guard(_Guard) -> undefined.  % TODO: Compile guard expressions

%% Compile action expression (placeholder)
compile_action(undefined) -> undefined;
compile_action(_Action) -> undefined.  % TODO: Compile action expressions

%% Find timeout transition in list of transitions
find_timeout_in_transitions([]) -> not_found;
find_timeout_in_transitions([#transition{event = {timeout, Timeout}, target = Target} | _]) ->
    {ok, {Timeout, Target}};
find_timeout_in_transitions([_ | Rest]) ->
    find_timeout_in_transitions(Rest).
