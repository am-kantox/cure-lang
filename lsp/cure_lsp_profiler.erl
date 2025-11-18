-module(cure_lsp_profiler).

%% Performance profiling for LSP SMT verification
%% Tracks cache hit rates, verification latency, and bottlenecks

-export([
    init/0,
    record_cache_hit/1,
    record_cache_miss/1,
    record_verification_time/2,
    record_z3_query_time/2,
    get_stats/1,
    reset_stats/1,
    format_stats/1
]).

-record(profiler_state, {
    % Cache statistics
    cache_hits = 0 :: non_neg_integer(),
    cache_misses = 0 :: non_neg_integer(),

    % Verification timing (microseconds)
    verification_times = [] :: [non_neg_integer()],
    verification_count = 0 :: non_neg_integer(),

    % Z3 query timing (microseconds)
    z3_query_times = [] :: [non_neg_integer()],
    z3_query_count = 0 :: non_neg_integer(),

    % Document statistics
    documents_verified = 0 :: non_neg_integer(),

    % Start time for session tracking
    start_time = undefined :: undefined | erlang:timestamp()
}).

-type profiler_state() :: #profiler_state{}.

%% ========================================================================
%% Public API
%% ========================================================================

-spec init() -> profiler_state().
init() ->
    #profiler_state{start_time = erlang:timestamp()}.

-spec record_cache_hit(profiler_state()) -> profiler_state().
record_cache_hit(State) ->
    State#profiler_state{cache_hits = State#profiler_state.cache_hits + 1}.

-spec record_cache_miss(profiler_state()) -> profiler_state().
record_cache_miss(State) ->
    State#profiler_state{cache_misses = State#profiler_state.cache_misses + 1}.

-spec record_verification_time(profiler_state(), non_neg_integer()) -> profiler_state().
record_verification_time(State, TimeMicros) ->
    Times = State#profiler_state.verification_times,
    % Keep only last 100 measurements to avoid unbounded growth
    NewTimes = lists:sublist([TimeMicros | Times], 100),
    State#profiler_state{
        verification_times = NewTimes,
        verification_count = State#profiler_state.verification_count + 1,
        documents_verified = State#profiler_state.documents_verified + 1
    }.

-spec record_z3_query_time(profiler_state(), non_neg_integer()) -> profiler_state().
record_z3_query_time(State, TimeMicros) ->
    Times = State#profiler_state.z3_query_times,
    % Keep only last 100 measurements
    NewTimes = lists:sublist([TimeMicros | Times], 100),
    State#profiler_state{
        z3_query_times = NewTimes,
        z3_query_count = State#profiler_state.z3_query_count + 1
    }.

-spec get_stats(profiler_state()) -> map().
get_stats(State) ->
    CacheHits = State#profiler_state.cache_hits,
    CacheMisses = State#profiler_state.cache_misses,
    TotalCacheAccess = CacheHits + CacheMisses,

    CacheHitRate =
        if
            TotalCacheAccess > 0 -> (CacheHits / TotalCacheAccess) * 100.0;
            true -> 0.0
        end,

    VerificationTimes = State#profiler_state.verification_times,
    Z3QueryTimes = State#profiler_state.z3_query_times,

    SessionDuration =
        case State#profiler_state.start_time of
            undefined -> 0;
            StartTime -> timer:now_diff(erlang:timestamp(), StartTime) / 1000000.0
        end,

    #{
        % Cache statistics
        cache_hits => CacheHits,
        cache_misses => CacheMisses,
        cache_hit_rate => CacheHitRate,

        % Verification timing
        verification_count => State#profiler_state.verification_count,
        verification_avg_ms => avg_time_ms(VerificationTimes),
        verification_p50_ms => percentile(VerificationTimes, 50),
        verification_p95_ms => percentile(VerificationTimes, 95),
        verification_p99_ms => percentile(VerificationTimes, 99),

        % Z3 query timing
        z3_query_count => State#profiler_state.z3_query_count,
        z3_query_avg_ms => avg_time_ms(Z3QueryTimes),
        z3_query_p50_ms => percentile(Z3QueryTimes, 50),
        z3_query_p95_ms => percentile(Z3QueryTimes, 95),
        z3_query_p99_ms => percentile(Z3QueryTimes, 99),

        % Document statistics
        documents_verified => State#profiler_state.documents_verified,

        % Session statistics
        session_duration_sec => SessionDuration,
        verifications_per_sec =>
            if
                SessionDuration > 0 -> State#profiler_state.verification_count / SessionDuration;
                true -> 0.0
            end
    }.

-spec reset_stats(profiler_state()) -> profiler_state().
reset_stats(_State) ->
    init().

-spec format_stats(profiler_state()) -> iolist().
format_stats(State) ->
    Stats = get_stats(State),

    [
        "=== LSP SMT Performance Statistics ===\n",
        "\n",
        "Cache Performance:\n",
        io_lib:format("  Cache Hits:      ~p\n", [maps:get(cache_hits, Stats)]),
        io_lib:format("  Cache Misses:    ~p\n", [maps:get(cache_misses, Stats)]),
        io_lib:format("  Cache Hit Rate:  ~.1f%\n", [maps:get(cache_hit_rate, Stats)]),
        "\n",
        "Verification Performance:\n",
        io_lib:format("  Total Verifications: ~p\n", [maps:get(verification_count, Stats)]),
        io_lib:format("  Average Time:        ~.2f ms\n", [maps:get(verification_avg_ms, Stats)]),
        io_lib:format("  P50 (Median):        ~.2f ms\n", [maps:get(verification_p50_ms, Stats)]),
        io_lib:format("  P95:                 ~.2f ms\n", [maps:get(verification_p95_ms, Stats)]),
        io_lib:format("  P99:                 ~.2f ms\n", [maps:get(verification_p99_ms, Stats)]),
        "\n",
        "Z3 Query Performance:\n",
        io_lib:format("  Total Z3 Queries:    ~p\n", [maps:get(z3_query_count, Stats)]),
        io_lib:format("  Average Time:        ~.2f ms\n", [maps:get(z3_query_avg_ms, Stats)]),
        io_lib:format("  P50 (Median):        ~.2f ms\n", [maps:get(z3_query_p50_ms, Stats)]),
        io_lib:format("  P95:                 ~.2f ms\n", [maps:get(z3_query_p95_ms, Stats)]),
        io_lib:format("  P99:                 ~.2f ms\n", [maps:get(z3_query_p99_ms, Stats)]),
        "\n",
        "Document Statistics:\n",
        io_lib:format("  Documents Verified:  ~p\n", [maps:get(documents_verified, Stats)]),
        "\n",
        "Session Statistics:\n",
        io_lib:format("  Session Duration:    ~.1f sec\n", [maps:get(session_duration_sec, Stats)]),
        io_lib:format("  Verifications/sec:   ~.2f\n", [maps:get(verifications_per_sec, Stats)]),
        "\n"
    ].

%% ========================================================================
%% Internal Functions
%% ========================================================================

%% Calculate average time in milliseconds
-spec avg_time_ms([non_neg_integer()]) -> float().
avg_time_ms([]) ->
    0.0;
avg_time_ms(Times) ->
    Sum = lists:sum(Times),
    % Convert microseconds to milliseconds
    (Sum / length(Times)) / 1000.0.

%% Calculate percentile from list of times
-spec percentile([non_neg_integer()], non_neg_integer()) -> float().
percentile([], _P) ->
    0.0;
percentile(Times, P) when P >= 0, P =< 100 ->
    Sorted = lists:sort(Times),
    Len = length(Sorted),
    Index = max(1, round((P / 100.0) * Len)),
    Value = lists:nth(Index, Sorted),
    % Convert microseconds to milliseconds
    Value / 1000.0.
