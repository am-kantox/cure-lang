%% Cure FSM Runtime - Header File
%% Record definitions for FSM runtime system

%% Performance statistics record
-record(fsm_perf_stats, {
    events_processed = 0 :: non_neg_integer(),
    avg_event_time = 0.0 :: float(),
    max_event_time = 0.0 :: float(),
    memory_usage = 0 :: non_neg_integer(),
    last_updated = 0 :: non_neg_integer()
}).

%% FSM definition record (compiled from AST)
-record(fsm_definition, {
    name,                  % FSM type name (atom)
    states,                % List of state names
    initial_state,         % Initial state name
    transitions,           % Transition table: #{State => #{Event => {Target, Guard, Action}}}
    timeouts               % Timeout table: #{State => {Timeout, Target}}
}).

%% FSM state record (runtime state for FSM process)
-record(fsm_state, {
    fsm_type :: atom(),
    current_state :: atom(),
    event_data :: term(),
    data :: term(),
    timeout_ref :: reference() | undefined,
    transitions :: term(),
    timeouts :: term(),
    event_history = [] :: [term()],
    perf_stats :: #fsm_perf_stats{} | undefined
}).
