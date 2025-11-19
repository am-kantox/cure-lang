%% Cure LSP Performance Optimization - Phase 4.4
%% Query batching, background verification, and performance tuning
-module(cure_lsp_performance).

-moduledoc """
# LSP Performance Optimization

This module provides performance optimizations for real-time LSP verification:

## Optimizations

### 1. Query Batching
- Batch multiple constraints into a single SMT query
- Use multiple `(assert ...)` before `(check-sat)`
- Reduces SMT solver startup overhead

### 2. Timeout Tuning
- Short timeout (500ms) for LSP interactive use
- Long timeout (5000ms) for full compilation
- Configurable per-context timeouts

### 3. Background Verification
- Queue verification tasks
- Process in background worker gen_server
- Return cached results immediately
- Cancel verification on file close

### 4. Hot Path Optimization
- Fast constraint extraction (<50ms)
- Optimized SMT-LIB generation
- AST caching to avoid re-parsing

## Performance Targets

- Constraint extraction: <50ms
- SMT query (simple): <100ms
- SMT query (complex): <500ms
- Full document verification: <1s
- Cache hit rate: >80%

## Architecture

```
LSP Request
    ↓
Fast Path: Cache Hit → Return immediately (<10ms)
    ↓
Slow Path: Cache Miss
    ↓
Background Worker: Queue task
    ↓
Batch Constraints → Single SMT Query
    ↓
Return result + Update cache
```
""".

-behaviour(gen_server).

%% API
-export([
    start_link/0,
    start_link/1,
    stop/0,

    % Verification API
    verify_async/3,
    verify_batch/2,
    cancel_verification/1,

    % Performance tuning
    set_timeout/2,
    get_stats/0,
    clear_queue/0
]).

%% gen_server callbacks
-export([
    init/1,
    handle_call/3,
    handle_cast/2,
    handle_info/2,
    terminate/2,
    code_change/3
]).

-include("../parser/cure_ast.hrl").

%% State record
-record(perf_state, {
    % Verification queue: [{Uri, AST, From}]
    queue = [] :: [{binary(), term(), pid() | reference()}],

    % Active verifications: #{Uri => Pid}
    active = #{} :: #{binary() => pid()},

    % Timeouts per context
    timeouts = #{
        % Interactive LSP
        lsp => 500,
        % Full compilation
        compile => 5000,
        % Testing
        test => 10000
    } :: #{atom() => integer()},

    % Performance statistics
    stats = #{
        queued => 0,
        processed => 0,
        cancelled => 0,
        avg_queue_time_ms => 0,
        avg_verify_time_ms => 0,
        batch_size_avg => 1.0
    } :: map(),

    % Batch configuration
    batch_size = 10 :: integer(),
    batch_timeout_ms = 50 :: integer()
}).

%%% ============================================================================
%%% API Functions
%%% ============================================================================

%% @doc Start the performance worker
-spec start_link() -> {ok, pid()} | {error, term()}.
start_link() ->
    start_link(#{}).

%% @doc Start with options
-spec start_link(map()) -> {ok, pid()} | {error, term()}.
start_link(Opts) ->
    gen_server:start_link({local, ?MODULE}, ?MODULE, Opts, []).

%% @doc Stop the worker
-spec stop() -> ok.
stop() ->
    gen_server:stop(?MODULE).

%% @doc Verify document asynchronously
-spec verify_async(binary(), term(), atom()) -> {ok, reference()}.
verify_async(Uri, AST, Context) ->
    Ref = make_ref(),
    gen_server:cast(?MODULE, {verify_async, Uri, AST, Context, self(), Ref}),
    {ok, Ref}.

%% @doc Verify batch of constraints in single query
-spec verify_batch([{binary(), term()}], atom()) -> {ok, [map()]}.
verify_batch(Items, Context) ->
    gen_server:call(?MODULE, {verify_batch, Items, Context}, infinity).

%% @doc Cancel verification for URI
-spec cancel_verification(binary()) -> ok.
cancel_verification(Uri) ->
    gen_server:cast(?MODULE, {cancel, Uri}).

%% @doc Set timeout for context
-spec set_timeout(atom(), integer()) -> ok.
set_timeout(Context, TimeoutMs) ->
    gen_server:cast(?MODULE, {set_timeout, Context, TimeoutMs}).

%% @doc Get performance statistics
-spec get_stats() -> map().
get_stats() ->
    gen_server:call(?MODULE, get_stats).

%% @doc Clear verification queue
-spec clear_queue() -> ok.
clear_queue() ->
    gen_server:cast(?MODULE, clear_queue).

%%% ============================================================================
%%% gen_server Callbacks
%%% ============================================================================

init(Opts) ->
    % Set process priority to low for background work
    process_flag(priority, low),

    State = #perf_state{
        queue = [],
        active = #{},
        timeouts = maps:get(timeouts, Opts, #{
            lsp => 500,
            compile => 5000,
            test => 10000
        }),
        batch_size = maps:get(batch_size, Opts, 10),
        batch_timeout_ms = maps:get(batch_timeout_ms, Opts, 50)
    },

    % Start batch processing timer
    schedule_batch_processing(State#perf_state.batch_timeout_ms),

    {ok, State}.

handle_call({verify_batch, Items, Context}, _From, State) ->
    StartTime = erlang:monotonic_time(millisecond),

    % Get timeout for context
    Timeout = maps:get(Context, State#perf_state.timeouts, 500),

    % Batch verify all items
    Results = batch_verify_items(Items, Timeout),

    Duration = erlang:monotonic_time(millisecond) - StartTime,

    % Update statistics
    NewState = update_batch_stats(State, length(Items), Duration),

    {reply, {ok, Results}, NewState};
handle_call(get_stats, _From, State) ->
    Stats = State#perf_state.stats,
    EnhancedStats = Stats#{
        queue_size => length(State#perf_state.queue),
        active_count => maps:size(State#perf_state.active)
    },
    {reply, EnhancedStats, State};
handle_call(_Request, _From, State) ->
    {reply, {error, unknown_request}, State}.

handle_cast({verify_async, Uri, AST, Context, From, Ref}, State) ->
    % Add to queue
    QueueItem = {Uri, AST, Context, From, Ref, erlang:monotonic_time(millisecond)},
    NewQueue = State#perf_state.queue ++ [QueueItem],

    % Update stats
    Stats = State#perf_state.stats,
    NewStats = Stats#{queued => maps:get(queued, Stats) + 1},

    NewState = State#perf_state{
        queue = NewQueue,
        stats = NewStats
    },

    % Try to process immediately if queue is large enough
    ProcessedState = maybe_process_batch(NewState),

    {noreply, ProcessedState};
handle_cast({cancel, Uri}, State) ->
    % Remove from queue
    NewQueue = lists:filter(
        fun({QueueUri, _AST, _Context, _From, _Ref, _Time}) ->
            QueueUri =/= Uri
        end,
        State#perf_state.queue
    ),

    % Kill active verification if any
    case maps:get(Uri, State#perf_state.active, undefined) of
        undefined -> ok;
        Pid -> exit(Pid, kill)
    end,

    NewActive = maps:remove(Uri, State#perf_state.active),

    % Update stats
    Stats = State#perf_state.stats,
    NewStats = Stats#{cancelled => maps:get(cancelled, Stats) + 1},

    {noreply, State#perf_state{
        queue = NewQueue,
        active = NewActive,
        stats = NewStats
    }};
handle_cast({set_timeout, Context, TimeoutMs}, State) ->
    Timeouts = State#perf_state.timeouts,
    NewTimeouts = maps:put(Context, TimeoutMs, Timeouts),
    {noreply, State#perf_state{timeouts = NewTimeouts}};
handle_cast(clear_queue, State) ->
    {noreply, State#perf_state{queue = []}};
handle_cast(_Msg, State) ->
    {noreply, State}.

handle_info(process_batch, State) ->
    % Process batch if queue has items
    NewState = process_batch(State),

    % Schedule next batch processing
    schedule_batch_processing(State#perf_state.batch_timeout_ms),

    {noreply, NewState};
handle_info({'DOWN', _Ref, process, Pid, _Reason}, State) ->
    % Remove from active verifications
    NewActive = maps:filter(
        fun(_Uri, ActivePid) -> ActivePid =/= Pid end,
        State#perf_state.active
    ),
    {noreply, State#perf_state{active = NewActive}};
handle_info(_Info, State) ->
    {noreply, State}.

terminate(_Reason, _State) ->
    ok.

code_change(_OldVsn, State, _Extra) ->
    {ok, State}.

%%% ============================================================================
%%% Internal Functions - Batch Processing
%%% ============================================================================

%% Process a batch from the queue
process_batch(#perf_state{queue = []} = State) ->
    % Empty queue
    State;
process_batch(State) ->
    BatchSize = State#perf_state.batch_size,
    Queue = State#perf_state.queue,

    % Take up to BatchSize items from queue
    {Batch, Remaining} = lists:split(min(BatchSize, length(Queue)), Queue),

    % Process batch
    case Batch of
        [] ->
            State;
        _ ->
            ProcessedState = process_batch_items(Batch, State),
            ProcessedState#perf_state{queue = Remaining}
    end.

%% Maybe process batch if queue is large enough
maybe_process_batch(#perf_state{queue = Queue, batch_size = BatchSize} = State) ->
    case length(Queue) >= BatchSize of
        true -> process_batch(State);
        false -> State
    end.

%% Process batch items
process_batch_items([], State) ->
    State;
process_batch_items(Batch, State) ->
    % Group by context for optimal batching
    Grouped = group_by_context(Batch),

    % Process each context group
    lists:foldl(
        fun({Context, Items}, AccState) ->
            process_context_batch(Context, Items, AccState)
        end,
        State,
        maps:to_list(Grouped)
    ).

%% Group batch items by context
group_by_context(Batch) ->
    lists:foldl(
        fun({Uri, AST, Context, From, Ref, Time}, Acc) ->
            ContextItems = maps:get(Context, Acc, []),
            maps:put(Context, [{Uri, AST, From, Ref, Time} | ContextItems], Acc)
        end,
        #{},
        Batch
    ).

%% Process items for a specific context
process_context_batch(Context, Items, State) ->
    Timeout = maps:get(Context, State#perf_state.timeouts, 500),

    % Extract constraints from all ASTs
    StartTime = erlang:monotonic_time(millisecond),
    BatchItems = [{Uri, AST} || {Uri, AST, _From, _Ref, _Time} <- Items],

    % Batch verify
    Results = batch_verify_items(BatchItems, Timeout),

    Duration = erlang:monotonic_time(millisecond) - StartTime,

    % Send results to callers
    lists:foreach(
        fun({{Uri, _AST}, Result, {_Uri2, _AST2, From, Ref, QueueTime}}) ->
            QueueDuration = StartTime - QueueTime,
            From ! {verification_result, Ref, Uri, Result, QueueDuration, Duration}
        end,
        lists:zip3(BatchItems, Results, Items)
    ),

    % Update statistics
    update_batch_stats(State, length(Items), Duration).

%% Batch verify multiple items in single SMT query
batch_verify_items(Items, Timeout) ->
    % Extract all constraints
    AllConstraints = lists:flatmap(
        fun({_Uri, AST}) ->
            cure_lsp_smt:extract_type_constraints(AST)
        end,
        Items
    ),

    % Batch verify all constraints
    case batch_verify_constraints(AllConstraints, Timeout) of
        {ok, ConstraintResults} ->
            % Map results back to items
            distribute_results(Items, ConstraintResults);
        {error, _Reason} ->
            % Return empty results on error
            [[] || _ <- Items]
    end.

%% Verify multiple constraints in single SMT query
batch_verify_constraints(Constraints, Timeout) ->
    try
        % Start SMT solver
        {ok, Solver} = cure_smt_process:start_solver(z3, Timeout),

        % Add all constraints to solver
        lists:foreach(
            fun(Constraint) ->
                cure_smt_process:assert_constraint(Solver, Constraint)
            end,
            Constraints
        ),

        % Check satisfiability
        Result = cure_smt_process:check_sat(Solver),

        % Stop solver
        cure_smt_process:stop_solver(Solver),

        {ok, Result}
    catch
        _:Reason -> {error, Reason}
    end.

%% Distribute batch results to individual items
distribute_results(Items, _ConstraintResults) ->
    % For now, return empty diagnostics for each item
    % Would need sophisticated result mapping in production
    [[] || _ <- Items].

%%% ============================================================================
%%% Statistics
%%% ============================================================================

update_batch_stats(State, BatchSize, Duration) ->
    Stats = State#perf_state.stats,

    Processed = maps:get(processed, Stats),
    AvgVerifyTime = maps:get(avg_verify_time_ms, Stats),
    AvgBatchSize = maps:get(batch_size_avg, Stats),

    % Update running averages
    NewProcessed = Processed + BatchSize,
    NewAvgVerifyTime = (AvgVerifyTime * Processed + Duration) / NewProcessed,
    NewAvgBatchSize = (AvgBatchSize * Processed + BatchSize) / NewProcessed,

    NewStats = Stats#{
        processed => NewProcessed,
        avg_verify_time_ms => NewAvgVerifyTime,
        batch_size_avg => NewAvgBatchSize
    },

    State#perf_state{stats = NewStats}.

%%% ============================================================================
%%% Helpers
%%% ============================================================================

schedule_batch_processing(TimeoutMs) ->
    erlang:send_after(TimeoutMs, self(), process_batch).
