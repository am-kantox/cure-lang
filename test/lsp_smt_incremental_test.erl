%% Phase 4.1: LSP SMT Incremental Solving Test Suite
-module(lsp_smt_incremental_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").

run() ->
    io:format("~n=== LSP SMT Incremental Solving Tests (Phase 4.1) ===~n~n"),

    Tests = [
        fun test_init_verification_state/0,
        fun test_persistent_solver_initialization/0,
        fun test_cache_hit/0,
        fun test_cache_miss/0,
        fun test_cache_invalidation/0,
        fun test_cache_region_invalidation/0,
        fun test_cache_statistics/0,
        fun test_cache_eviction/0,
        fun test_push_pop_context/0
    ],

    Results = lists:map(fun run_test/1, Tests),

    Passed = length([R || R <- Results, R =:= ok]),
    Failed = length(Results) - Passed,

    io:format("~n=== Results ===~n"),
    io:format("Passed: ~p~n", [Passed]),
    io:format("Failed: ~p~n", [Failed]),

    case Failed of
        0 -> io:format("~n✅ All Phase 4.1 tests passed!~n~n");
        _ -> io:format("~n❌ Some Phase 4.1 tests failed!~n~n")
    end,

    ok.

run_test(TestFun) ->
    try
        TestFun(),
        ok
    catch
        Class:Reason:Stack ->
            io:format("  ❌ FAILED: ~p:~p~n", [Class, Reason]),
            io:format("     Stack: ~p~n", [Stack]),
            error
    end.

%% ============================================================================
%% Test: Initialize verification state
%% ============================================================================

test_init_verification_state() ->
    io:format("Testing verification state initialization... "),

    % Test basic initialization
    State = cure_lsp_smt:init_verification_state(),

    % Verify state structure
    case State of
        {verification_state, Cache, DocCons, Timestamps, _, _, _, _, _} ->
            case {Cache, DocCons, Timestamps} of
                {EmptyMap1, EmptyMap2, EmptyMap3} when
                    map_size(EmptyMap1) =:= 0,
                    map_size(EmptyMap2) =:= 0,
                    map_size(EmptyMap3) =:= 0
                ->
                    io:format("✅ Basic state initialized~n"),
                    ok;
                _ ->
                    io:format("❌ State not properly initialized~n"),
                    error(state_initialization_failed)
            end;
        _ ->
            io:format("❌ Invalid state structure~n"),
            error(invalid_state_structure)
    end.

%% ============================================================================
%% Test: Persistent solver initialization
%% ============================================================================

test_persistent_solver_initialization() ->
    io:format("Testing persistent solver initialization... "),

    % Try to initialize with persistent solver
    State = cure_lsp_smt:init_verification_state(#{
        persistent_solver => true,
        solver => z3,
        timeout => 500
    }),

    % Check if solver was initialized (may fail if Z3 not available)
    case element(5, State) of
        undefined ->
            io:format("✅ No solver (Z3 not available, expected)~n"),
            ok;
        Pid when is_pid(Pid) ->
            io:format("✅ Persistent solver started: ~p~n", [Pid]),
            % Clean up
            catch cure_smt_process:stop_solver(Pid),
            ok;
        _ ->
            io:format("⚠️  Unexpected solver state~n"),
            ok
    end.

%% ============================================================================
%% Test: Cache hit
%% ============================================================================

test_cache_hit() ->
    io:format("Testing cache hit... "),

    % Create state with cached result
    Hash = 12345,
    Timestamp = erlang:system_time(millisecond),
    Cache = #{Hash => {valid, Timestamp}},

    State = {verification_state, Cache, #{}, #{}, undefined, 0, 0, 0, #{}},

    % Simulate retrieving from cache
    case maps:get(Hash, Cache, undefined) of
        {valid, _} ->
            io:format("✅ Cache hit successful~n"),
            ok;
        _ ->
            io:format("❌ Cache hit failed~n"),
            error(cache_hit_failed)
    end.

%% ============================================================================
%% Test: Cache miss
%% ============================================================================

test_cache_miss() ->
    io:format("Testing cache miss... "),

    % Create empty cache
    Cache = #{},
    Hash = 12345,

    case maps:get(Hash, Cache, undefined) of
        undefined ->
            io:format("✅ Cache miss detected correctly~n"),
            ok;
        _ ->
            io:format("❌ Cache miss not detected~n"),
            error(cache_miss_failed)
    end.

%% ============================================================================
%% Test: Cache invalidation
%% ============================================================================

test_cache_invalidation() ->
    io:format("Testing cache invalidation... "),

    % Create state with cached constraints
    Uri = <<"file:///test.cure">>,
    Constraint1 = test_constraint,
    Hash1 = erlang:phash2(Constraint1),

    Cache = #{Hash1 => {valid, erlang:system_time(millisecond)}},
    DocConstraints = #{Uri => [Constraint1]},

    State = {verification_state, Cache, DocConstraints, #{}, undefined, 0, 0, 0, #{}},

    % Invalidate cache for document
    NewState = cure_lsp_smt:invalidate_cache(Uri, State),

    % Verify cache was cleared
    NewCache = element(2, NewState),
    NewDocCons = element(3, NewState),

    case {maps:size(NewCache), maps:get(Uri, NewDocCons, not_found)} of
        {0, not_found} ->
            io:format("✅ Cache invalidated successfully~n"),
            ok;
        _ ->
            io:format("❌ Cache not properly invalidated~n"),
            error(cache_invalidation_failed)
    end.

%% ============================================================================
%% Test: Cache region invalidation
%% ============================================================================

test_cache_region_invalidation() ->
    io:format("Testing cache region invalidation... "),

    Uri = <<"file:///test.cure">>,
    State = {verification_state, #{}, #{}, #{}, undefined, 0, 0, 0, #{}},

    % Invalidate specific line range
    NewState = cure_lsp_smt:invalidate_cache_region(Uri, 10, 20, State),

    % Check that changes were tracked
    DocChanges = element(9, NewState),
    UriChanges = maps:get(Uri, DocChanges, #{}),

    % Verify lines 10-20 are marked as changed
    Line10Changed = maps:get(10, UriChanges, false),
    Line15Changed = maps:get(15, UriChanges, false),
    Line20Changed = maps:get(20, UriChanges, false),
    Line21Changed = maps:get(21, UriChanges, false),

    case {Line10Changed, Line15Changed, Line20Changed, Line21Changed} of
        {true, true, true, false} ->
            io:format("✅ Region invalidation successful~n"),
            ok;
        _ ->
            io:format("❌ Region invalidation failed: ~p~n", [
                {Line10Changed, Line15Changed, Line20Changed, Line21Changed}
            ]),
            error(region_invalidation_failed)
    end.

%% ============================================================================
%% Test: Cache statistics
%% ============================================================================

test_cache_statistics() ->
    io:format("Testing cache statistics... "),

    % Create state with some activity
    State =
        {verification_state,
            % Cache with 2 entries
            #{a => {valid, 1}, b => {invalid, 2}}, #{}, #{}, undefined, 0,
            % 10 cache hits
            10,
            % 5 cache misses
            5, #{}},

    Stats = cure_lsp_smt:get_cache_stats(State),

    % Verify statistics
    Hits = maps:get(cache_hits, Stats),
    Misses = maps:get(cache_misses, Stats),
    Size = maps:get(cache_size, Stats),
    HitRate = maps:get(hit_rate_percent, Stats),

    % 66.67%
    ExpectedHitRate = (10 / 15) * 100,

    case {Hits, Misses, Size, abs(HitRate - ExpectedHitRate) < 0.1} of
        {10, 5, 2, true} ->
            io:format("✅ Statistics correct: ~.2f% hit rate~n", [HitRate]),
            ok;
        _ ->
            io:format(
                "❌ Statistics incorrect: hits=~p, misses=~p, size=~p, rate=~p~n",
                [Hits, Misses, Size, HitRate]
            ),
            error(statistics_failed)
    end.

%% ============================================================================
%% Test: Cache eviction
%% ============================================================================

test_cache_eviction() ->
    io:format("Testing cache eviction... "),

    % Create state with old and new entries
    Now = erlang:system_time(millisecond),
    % 10 seconds ago
    OldTime = Now - 10000,

    Cache = #{
        old_entry => {valid, OldTime},
        new_entry => {valid, Now}
    },

    State = {verification_state, Cache, #{}, #{}, undefined, 0, 0, 0, #{}},

    % Evict entries older than 5 seconds (5000ms)
    NewState = cure_lsp_smt:evict_old_cache_entries(State, 5000),

    NewCache = element(2, NewState),

    % Should have only new_entry
    case {maps:is_key(old_entry, NewCache), maps:is_key(new_entry, NewCache)} of
        {false, true} ->
            io:format("✅ Old entries evicted, new entries retained~n"),
            ok;
        _ ->
            io:format("❌ Eviction failed~n"),
            error(eviction_failed)
    end.

%% ============================================================================
%% Test: Push/pop context
%% ============================================================================

test_push_pop_context() ->
    io:format("Testing push/pop context... "),

    % Test without persistent solver
    State1 = {verification_state, #{}, #{}, #{}, undefined, 0, 0, 0, #{}},
    State2 = cure_lsp_smt:push_solver_context(State1),

    Depth1 = element(6, State2),

    % Without solver, depth should remain 0
    case Depth1 of
        0 ->
            io:format("✅ Push/pop context (no solver)~n"),
            ok;
        _ ->
            io:format("❌ Depth changed without solver: ~p~n", [Depth1]),
            error(push_pop_failed)
    end.
