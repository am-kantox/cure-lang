%% Cure Programming Language - Runtime Profiler
%% Collects execution statistics for profile-guided optimization
-module(cure_profiler).

-moduledoc """
# Cure Runtime Profiler

Collects runtime execution statistics to guide compiler optimizations.
Provides lightweight instrumentation and aggregation of:
- Function call counts and frequencies
- Hot path detection through call sequences
- Type usage patterns at runtime
- Memory allocation patterns
- Performance metrics

## Usage

```erlang
% Initialize profiling
cure_profiler:start_profiling(),

% Run your code
my_application:run(),

% Collect profile data
ProfileData = cure_profiler:get_profile_data(),

% Use for optimization
OptimizedAST = cure_type_optimizer:optimize_with_profile(AST, ProfileData),

% Stop profiling
cure_profiler:stop_profiling().
```

## Profile Data Format

Profile data is stored as a map with the following structure:
```erlang
#{
    function_calls => #{FunctionName => CallCount},
    call_sequences => [{Caller, Callee, Count}],
    type_usage => #{Type => UsageCount},
    memory_allocations => #{Function => AllocationSize},
    hot_functions => [FunctionName],
    hot_paths => [[FunctionName]],
    timestamp => Milliseconds
}
```
""".

-export([
    % Profiling lifecycle
    start_profiling/0,
    start_profiling/1,
    stop_profiling/0,
    reset_profiling/0,

    % Data collection
    record_function_call/1,
    record_function_call/2,
    record_call_sequence/2,
    record_type_usage/2,
    record_memory_allocation/2,

    % Profile data retrieval
    get_profile_data/0,
    get_function_stats/0,
    get_hot_functions/0,
    get_hot_functions/1,
    get_hot_paths/0,
    get_type_usage/0,

    % Analysis
    analyze_profile/0,
    analyze_profile/1,
    export_profile/1,
    import_profile/1
]).

%% ETS table names
-define(PROFILE_TABLE, cure_profile_data).
-define(CALL_SEQUENCE_TABLE, cure_call_sequences).
-define(TYPE_USAGE_TABLE, cure_type_usage).
-define(MEMORY_TABLE, cure_memory_allocations).

%% Profiling state
-define(PROFILING_KEY, profiling_enabled).
-define(START_TIME_KEY, start_time).
-define(CALL_STACK_KEY, call_stack).

%% ============================================================================
%% Public API - Profiling Lifecycle
%% ============================================================================

%% @doc Start profiling with default configuration
-spec start_profiling() -> ok.
start_profiling() ->
    start_profiling(#{}).

%% @doc Start profiling with custom configuration
-spec start_profiling(map()) -> ok.
start_profiling(Config) ->
    % Initialize ETS tables
    init_profile_tables(),

    % Store configuration
    put(?PROFILING_KEY, true),
    put(?START_TIME_KEY, erlang:system_time(millisecond)),
    put(?CALL_STACK_KEY, []),

    % Store config in table for persistence
    ets:insert(?PROFILE_TABLE, {config, Config}),

    ok.

%% @doc Stop profiling and finalize data
-spec stop_profiling() -> ok.
stop_profiling() ->
    case get(?PROFILING_KEY) of
        true ->
            Duration = erlang:system_time(millisecond) - get(?START_TIME_KEY),
            ets:insert(?PROFILE_TABLE, {duration, Duration}),
            put(?PROFILING_KEY, false),
            ok;
        _ ->
            ok
    end.

%% @doc Reset all profiling data
-spec reset_profiling() -> ok.
reset_profiling() ->
    case ets:info(?PROFILE_TABLE) of
        undefined -> ok;
        _ -> ets:delete_all_objects(?PROFILE_TABLE)
    end,
    case ets:info(?CALL_SEQUENCE_TABLE) of
        undefined -> ok;
        _ -> ets:delete_all_objects(?CALL_SEQUENCE_TABLE)
    end,
    case ets:info(?TYPE_USAGE_TABLE) of
        undefined -> ok;
        _ -> ets:delete_all_objects(?TYPE_USAGE_TABLE)
    end,
    case ets:info(?MEMORY_TABLE) of
        undefined -> ok;
        _ -> ets:delete_all_objects(?MEMORY_TABLE)
    end,
    ok.

%% ============================================================================
%% Public API - Data Collection
%% ============================================================================

%% @doc Record a function call
-spec record_function_call(atom()) -> ok.
record_function_call(FunctionName) ->
    record_function_call(FunctionName, 1).

%% @doc Record a function call with custom count
-spec record_function_call(atom(), pos_integer()) -> ok.
record_function_call(FunctionName, Count) ->
    case is_profiling_enabled() of
        true ->
            % Update call count
            ets:update_counter(?PROFILE_TABLE, FunctionName, {2, Count}, {FunctionName, 0}),

            % Update call stack for sequence tracking
            CallStack = get(?CALL_STACK_KEY),
            case CallStack of
                [Caller | _] ->
                    record_call_sequence(Caller, FunctionName);
                [] ->
                    ok
            end,

            % Push to call stack
            put(?CALL_STACK_KEY, [FunctionName | CallStack]),
            ok;
        false ->
            ok
    end.

%% @doc Record a call sequence (caller -> callee)
-spec record_call_sequence(atom(), atom()) -> ok.
record_call_sequence(Caller, Callee) ->
    case is_profiling_enabled() of
        true ->
            Key = {Caller, Callee},
            ets:update_counter(?CALL_SEQUENCE_TABLE, Key, {2, 1}, {Key, 0}),
            ok;
        false ->
            ok
    end.

%% @doc Record type usage
-spec record_type_usage(atom(), term()) -> ok.
record_type_usage(FunctionName, Type) ->
    case is_profiling_enabled() of
        true ->
            Key = {FunctionName, Type},
            ets:update_counter(?TYPE_USAGE_TABLE, Key, {2, 1}, {Key, 0}),
            ok;
        false ->
            ok
    end.

%% @doc Record memory allocation
-spec record_memory_allocation(atom(), non_neg_integer()) -> ok.
record_memory_allocation(FunctionName, Size) ->
    case is_profiling_enabled() of
        true ->
            ets:update_counter(?MEMORY_TABLE, FunctionName, {2, Size}, {FunctionName, 0}),
            ok;
        false ->
            ok
    end.

%% ============================================================================
%% Public API - Profile Data Retrieval
%% ============================================================================

%% @doc Get complete profile data
-spec get_profile_data() -> map().
get_profile_data() ->
    FunctionStats = get_function_stats(),
    CallSequences = get_call_sequences(),
    TypeUsage = get_type_usage(),
    MemoryAllocations = get_memory_allocations(),
    HotFunctions = get_hot_functions(),
    HotPaths = get_hot_paths(),

    [{_, Duration}] = ets:lookup(?PROFILE_TABLE, duration),
    [{_, Config}] = ets:lookup(?PROFILE_TABLE, config),

    #{
        function_calls => FunctionStats,
        call_sequences => CallSequences,
        type_usage => TypeUsage,
        memory_allocations => MemoryAllocations,
        hot_functions => HotFunctions,
        hot_paths => HotPaths,
        duration_ms => Duration,
        config => Config,
        timestamp => erlang:system_time(millisecond)
    }.

%% @doc Get function call statistics
-spec get_function_stats() -> map().
get_function_stats() ->
    Stats = ets:select(?PROFILE_TABLE, [{{' $1', '$2'}, [], [{{'$1', '$2'}}]}]),
    FilteredStats = lists:filter(
        fun({Key, _}) -> is_atom(Key) andalso Key =/= config andalso Key =/= duration end,
        Stats
    ),
    maps:from_list(FilteredStats).

%% @doc Get hot functions (most frequently called)
-spec get_hot_functions() -> [atom()].
get_hot_functions() ->
    get_hot_functions(10).

%% @doc Get top N hot functions
-spec get_hot_functions(pos_integer()) -> [atom()].
get_hot_functions(N) ->
    Stats = get_function_stats(),
    Sorted = lists:sort(fun({_, C1}, {_, C2}) -> C1 >= C2 end, maps:to_list(Stats)),
    TopN = lists:sublist(Sorted, N),
    [FuncName || {FuncName, _Count} <- TopN].

%% @doc Get hot execution paths
-spec get_hot_paths() -> [[atom()]].
get_hot_paths() ->
    CallSequences = get_call_sequences(),
    % Build call graph
    CallGraph = build_call_graph(CallSequences),
    % Find frequently executed paths (3+ functions deep)
    extract_hot_paths(CallGraph, 3).

%% @doc Get type usage statistics
-spec get_type_usage() -> map().
get_type_usage() ->
    TypeStats = ets:tab2list(?TYPE_USAGE_TABLE),
    maps:from_list([{Key, Count} || {Key, Count} <- TypeStats]).

%% ============================================================================
%% Public API - Analysis
%% ============================================================================

%% @doc Analyze profile data and generate optimization suggestions
-spec analyze_profile() -> map().
analyze_profile() ->
    analyze_profile(#{}).

%% @doc Analyze profile data with custom thresholds
-spec analyze_profile(map()) -> map().
analyze_profile(Opts) ->
    HotThreshold = maps:get(hot_threshold, Opts, 100),

    FunctionStats = get_function_stats(),
    HotFunctions = get_hot_functions(),
    HotPaths = get_hot_paths(),
    TypeUsage = get_type_usage(),

    % Calculate suggestions
    InliningCandidates = identify_inlining_candidates(FunctionStats, HotFunctions),
    SpecializationCandidates = identify_specialization_candidates(TypeUsage, FunctionStats),
    HotPathOptimizations = identify_hot_path_optimizations(HotPaths, HotThreshold),

    #{
        summary => #{
            total_function_calls => maps:size(FunctionStats),
            total_hot_functions => length(HotFunctions),
            total_hot_paths => length(HotPaths),
            unique_types => count_unique_types(TypeUsage)
        },
        suggestions => #{
            inlining => InliningCandidates,
            specialization => SpecializationCandidates,
            hot_path_opts => HotPathOptimizations
        }
    }.

%% @doc Export profile data to file
-spec export_profile(file:filename()) -> ok | {error, term()}.
export_profile(Filename) ->
    ProfileData = get_profile_data(),
    Binary = term_to_binary(ProfileData, [compressed]),
    file:write_file(Filename, Binary).

%% @doc Import profile data from file
-spec import_profile(file:filename()) -> ok | {error, term()}.
import_profile(Filename) ->
    case file:read_file(Filename) of
        {ok, Binary} ->
            ProfileData = binary_to_term(Binary),
            restore_profile_data(ProfileData),
            ok;
        Error ->
            Error
    end.

%% ============================================================================
%% Internal Functions
%% ============================================================================

%% Initialize ETS tables for profiling
init_profile_tables() ->
    case ets:info(?PROFILE_TABLE) of
        undefined ->
            ets:new(?PROFILE_TABLE, [named_table, public, set]);
        _ ->
            ok
    end,
    case ets:info(?CALL_SEQUENCE_TABLE) of
        undefined ->
            ets:new(?CALL_SEQUENCE_TABLE, [named_table, public, set]);
        _ ->
            ok
    end,
    case ets:info(?TYPE_USAGE_TABLE) of
        undefined ->
            ets:new(?TYPE_USAGE_TABLE, [named_table, public, set]);
        _ ->
            ok
    end,
    case ets:info(?MEMORY_TABLE) of
        undefined ->
            ets:new(?MEMORY_TABLE, [named_table, public, set]);
        _ ->
            ok
    end,
    ok.

%% Check if profiling is currently enabled
is_profiling_enabled() ->
    get(?PROFILING_KEY) =:= true.

%% Get call sequences
get_call_sequences() ->
    Sequences = ets:tab2list(?CALL_SEQUENCE_TABLE),
    [{{Caller, Callee}, Count} || {{Caller, Callee}, Count} <- Sequences].

%% Get memory allocations
get_memory_allocations() ->
    Allocations = ets:tab2list(?MEMORY_TABLE),
    maps:from_list(Allocations).

%% Build call graph from sequences
build_call_graph(CallSequences) ->
    lists:foldl(
        fun({{Caller, Callee}, Count}, Graph) ->
            Edges = maps:get(Caller, Graph, []),
            maps:put(Caller, [{Callee, Count} | Edges], Graph)
        end,
        #{},
        CallSequences
    ).

%% Extract hot paths from call graph
extract_hot_paths(CallGraph, MinDepth) ->
    % DFS to find paths of at least MinDepth
    Nodes = maps:keys(CallGraph),
    lists:flatmap(
        fun(StartNode) ->
            find_paths_from_node(StartNode, CallGraph, MinDepth, [StartNode], [])
        end,
        Nodes
    ).

find_paths_from_node(CurrentNode, CallGraph, MinDepth, Path, Acc) ->
    case length(Path) >= MinDepth of
        true ->
            % Valid path found
            NewAcc = [lists:reverse(Path) | Acc],
            % Continue exploring
            case maps:get(CurrentNode, CallGraph, []) of
                [] ->
                    NewAcc;
                Edges ->
                    lists:foldl(
                        fun({NextNode, _Count}, PathAcc) ->
                            case lists:member(NextNode, Path) of
                                % Avoid cycles
                                true ->
                                    PathAcc;
                                false ->
                                    find_paths_from_node(
                                        NextNode,
                                        CallGraph,
                                        MinDepth,
                                        [NextNode | Path],
                                        PathAcc
                                    )
                            end
                        end,
                        NewAcc,
                        Edges
                    )
            end;
        false ->
            % Path too short, continue exploring
            case maps:get(CurrentNode, CallGraph, []) of
                [] ->
                    Acc;
                Edges ->
                    lists:foldl(
                        fun({NextNode, _Count}, PathAcc) ->
                            case lists:member(NextNode, Path) of
                                % Avoid cycles
                                true ->
                                    PathAcc;
                                false ->
                                    find_paths_from_node(
                                        NextNode,
                                        CallGraph,
                                        MinDepth,
                                        [NextNode | Path],
                                        PathAcc
                                    )
                            end
                        end,
                        Acc,
                        Edges
                    )
            end
    end.

%% Identify inlining candidates
identify_inlining_candidates(FunctionStats, HotFunctions) ->
    % Functions that are hot but small enough to inline
    lists:filter(
        fun(FuncName) ->
            CallCount = maps:get(FuncName, FunctionStats, 0),
            % Hot enough to benefit from inlining
            CallCount > 50
        end,
        HotFunctions
    ).

%% Identify specialization candidates
identify_specialization_candidates(TypeUsage, FunctionStats) ->
    % Functions with diverse type usage that could benefit from specialization
    TypesByFunction = group_types_by_function(TypeUsage),
    maps:fold(
        fun(FuncName, Types, Acc) ->
            case length(Types) >= 2 andalso maps:is_key(FuncName, FunctionStats) of
                true ->
                    CallCount = maps:get(FuncName, FunctionStats),
                    case CallCount > 25 of
                        true -> [{FuncName, Types, CallCount} | Acc];
                        false -> Acc
                    end;
                false ->
                    Acc
            end
        end,
        [],
        TypesByFunction
    ).

%% Identify hot path optimizations
identify_hot_path_optimizations(HotPaths, Threshold) ->
    % Return paths that would benefit from optimization
    lists:filter(
        fun(Path) -> length(Path) >= 3 end,
        HotPaths
    ).

%% Group types by function
group_types_by_function(TypeUsage) ->
    maps:fold(
        fun({FuncName, Type}, _Count, Acc) ->
            Types = maps:get(FuncName, Acc, []),
            maps:put(FuncName, [Type | Types], Acc)
        end,
        #{},
        TypeUsage
    ).

%% Count unique types
count_unique_types(TypeUsage) ->
    Types = [Type || {{_Func, Type}, _Count} <- maps:to_list(TypeUsage)],
    length(lists:usort(Types)).

%% Restore profile data from imported file
restore_profile_data(ProfileData) ->
    reset_profiling(),

    FunctionCalls = maps:get(function_calls, ProfileData, #{}),
    maps:foreach(
        fun(Func, Count) ->
            ets:insert(?PROFILE_TABLE, {Func, Count})
        end,
        FunctionCalls
    ),

    CallSequences = maps:get(call_sequences, ProfileData, []),
    lists:foreach(
        fun({{Caller, Callee}, Count}) ->
            ets:insert(?CALL_SEQUENCE_TABLE, {{Caller, Callee}, Count})
        end,
        CallSequences
    ),

    TypeUsage = maps:get(type_usage, ProfileData, #{}),
    maps:foreach(
        fun(Key, Count) ->
            ets:insert(?TYPE_USAGE_TABLE, {Key, Count})
        end,
        TypeUsage
    ),

    ok.
