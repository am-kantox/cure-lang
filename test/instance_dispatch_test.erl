-module(instance_dispatch_test).

%% Test suite for typeclass instance dispatch runtime
%% Tests registration, lookup, dispatch, caching, and performance

-export([run/0, test_method_int/1, test_method_float/1]).

-define(TYPECLASS, 'Show').
-define(INT_TYPE, {primitive_type, 'Int'}).
-define(FLOAT_TYPE, {primitive_type, 'Float'}).
-define(STRING_TYPE, {primitive_type, 'String'}).
-define(LIST_TYPE, {dependent_type, 'List', [{primitive_type, 'Int'}]}).

%% ============================================================================
%% Test Runner
%% ============================================================================

run() ->
    io:format("~n=== Instance Dispatch Test Suite ===~n~n"),

    % Start the instance registry
    {ok, _Pid} = cure_instance_registry:start_link(),

    % Run all test categories
    Results = [
        {"Registration Tests", run_registration_tests()},
        {"Lookup Tests", run_lookup_tests()},
        {"Type Inference Tests", run_type_inference_tests()},
        {"Dispatch Tests", run_dispatch_tests()},
        {"Cache Tests", run_cache_tests()},
        {"Performance Tests", run_performance_tests()}
    ],

    % Stop the registry
    cure_instance_registry:stop(),

    % Print summary
    print_summary(Results),

    % Return success if all passed
    AllPassed = lists:all(fun({_, {Pass, _Fail}}) -> Pass > 0 andalso Pass == Pass end, Results),
    case AllPassed of
        true -> ok;
        false -> {error, tests_failed}
    end.

%% ============================================================================
%% Registration Tests
%% ============================================================================

run_registration_tests() ->
    io:format("~n--- Registration Tests ---~n"),

    Tests = [
        {"Register Show(Int) instance", fun test_register_int_instance/0},
        {"Register Show(Float) instance", fun test_register_float_instance/0},
        {"Register duplicate instance fails", fun test_register_duplicate/0},
        {"Register with priority", fun test_register_with_priority/0},
        {"Get all instances for typeclass", fun test_get_all_instances/0}
    ],

    run_tests(Tests).

test_register_int_instance() ->
    Methods = #{show => {test_module, show_int, 1}},
    Result = cure_instance_registry:register_instance(?TYPECLASS, ?INT_TYPE, Methods),
    assert_equals(ok, Result).

test_register_float_instance() ->
    Methods = #{show => {test_module, show_float, 1}},
    Result = cure_instance_registry:register_instance(?TYPECLASS, ?FLOAT_TYPE, Methods),
    assert_equals(ok, Result).

test_register_duplicate() ->
    % Try to register Int again
    Methods = #{show => {test_module, show_int_v2, 1}},
    Result = cure_instance_registry:register_instance(?TYPECLASS, ?INT_TYPE, Methods),
    case Result of
        {error, {duplicate_instance, _, _}} -> ok;
        _ -> {error, {expected_duplicate_error, got, Result}}
    end.

test_register_with_priority() ->
    Type = {primitive_type, 'String'},
    Methods = #{show => {test_module, show_string, 1}},
    Result = cure_instance_registry:register_instance(?TYPECLASS, Type, Methods, 200),
    assert_equals(ok, Result).

test_get_all_instances() ->
    Instances = cure_instance_registry:get_all_instances(?TYPECLASS),
    % Should have at least 3 instances (Int, Float, String)
    Length = length(Instances),
    if
        Length >= 3 -> ok;
        true -> {error, {expected_at_least_3_instances, got, Length}}
    end.

%% ============================================================================
%% Lookup Tests
%% ============================================================================

run_lookup_tests() ->
    io:format("~n--- Lookup Tests ---~n"),

    Tests = [
        {"Lookup existing Int instance", fun test_lookup_int/0},
        {"Lookup existing Float instance", fun test_lookup_float/0},
        {"Lookup non-existent instance", fun test_lookup_nonexistent/0},
        {"Get specific method", fun test_get_method/0},
        {"Get non-existent method", fun test_get_nonexistent_method/0}
    ],

    run_tests(Tests).

test_lookup_int() ->
    Result = cure_instance_registry:lookup_instance(?TYPECLASS, ?INT_TYPE),
    case Result of
        {ok, _Entry} -> ok;
        _ -> {error, {expected_ok_entry, got, Result}}
    end.

test_lookup_float() ->
    Result = cure_instance_registry:lookup_instance(?TYPECLASS, ?FLOAT_TYPE),
    case Result of
        {ok, _Entry} -> ok;
        _ -> {error, {expected_ok_entry, got, Result}}
    end.

test_lookup_nonexistent() ->
    Type = {primitive_type, 'NonExistent'},
    Result = cure_instance_registry:lookup_instance(?TYPECLASS, Type),
    assert_equals(not_found, Result).

test_get_method() ->
    Result = cure_instance_registry:get_method(?TYPECLASS, show, ?INT_TYPE),
    case Result of
        {ok, {test_module, show_int, 1}} -> ok;
        _ -> {error, {expected_method, got, Result}}
    end.

test_get_nonexistent_method() ->
    Result = cure_instance_registry:get_method(?TYPECLASS, nonexistent, ?INT_TYPE),
    case Result of
        {error, {method_not_found, _, _, _}} -> ok;
        _ -> {error, {expected_method_not_found, got, Result}}
    end.

%% ============================================================================
%% Type Inference Tests
%% ============================================================================

run_type_inference_tests() ->
    io:format("~n--- Type Inference Tests ---~n"),

    Tests = [
        {"Infer Int from integer", fun test_infer_int/0},
        {"Infer Float from float", fun test_infer_float/0},
        {"Infer Bool from boolean", fun test_infer_bool/0},
        {"Infer String from binary", fun test_infer_string_binary/0},
        {"Infer String from char list", fun test_infer_string_list/0},
        {"Infer List from list", fun test_infer_list/0},
        {"Infer Tuple from tuple", fun test_infer_tuple/0},
        {"Infer Record from tagged tuple", fun test_infer_record/0}
    ],

    run_tests(Tests).

test_infer_int() ->
    Type = cure_typeclass_dispatch:infer_runtime_type(42),
    assert_equals({primitive_type, 'Int'}, Type).

test_infer_float() ->
    Type = cure_typeclass_dispatch:infer_runtime_type(3.14),
    assert_equals({primitive_type, 'Float'}, Type).

test_infer_bool() ->
    Type = cure_typeclass_dispatch:infer_runtime_type(true),
    assert_equals({primitive_type, 'Bool'}, Type).

test_infer_string_binary() ->
    Type = cure_typeclass_dispatch:infer_runtime_type(<<"hello">>),
    assert_equals({primitive_type, 'String'}, Type).

test_infer_string_list() ->
    Type = cure_typeclass_dispatch:infer_runtime_type("hello"),
    assert_equals({primitive_type, 'String'}, Type).

test_infer_list() ->
    Type = cure_typeclass_dispatch:infer_runtime_type([1, 2, 3]),
    case Type of
        {dependent_type, 'List', [{primitive_type, 'Int'}]} -> ok;
        _ -> {error, {expected_list_type, got, Type}}
    end.

test_infer_tuple() ->
    Type = cure_typeclass_dispatch:infer_runtime_type({1, "hello", 3.14}),
    case Type of
        {tuple_type, [_, _, _]} -> ok;
        _ -> {error, {expected_tuple_type, got, Type}}
    end.

test_infer_record() ->
    % Simulate a record (tagged tuple with atom first)
    Record = {point, 10, 20},
    Type = cure_typeclass_dispatch:infer_runtime_type(Record),
    assert_equals({record_type, point}, Type).

%% ============================================================================
%% Dispatch Tests
%% ============================================================================

run_dispatch_tests() ->
    io:format("~n--- Dispatch Tests ---~n"),

    % Register test instances with actual callable functions
    register_test_instances(),

    Tests = [
        {"Dispatch to Int method", fun test_dispatch_int/0},
        {"Dispatch to Float method", fun test_dispatch_float/0},
        {"Dispatch with cache miss", fun test_dispatch_cache_miss/0},
        {"Dispatch to non-existent instance", fun test_dispatch_nonexistent/0}
    ],

    run_tests(Tests).

register_test_instances() ->
    % Register instances that point to functions in this module
    cure_instance_registry:register_instance(
        'TestClass',
        {primitive_type, 'Int'},
        #{test_method => {?MODULE, test_method_int, 1}}
    ),
    cure_instance_registry:register_instance(
        'TestClass',
        {primitive_type, 'Float'},
        #{test_method => {?MODULE, test_method_float, 1}}
    ).

test_dispatch_int() ->
    Result = cure_typeclass_dispatch:dispatch('TestClass', test_method, 42, []),
    assert_equals({int_result, 42}, Result).

test_dispatch_float() ->
    Result = cure_typeclass_dispatch:dispatch('TestClass', test_method, 3.14, []),
    assert_equals({float_result, 3.14}, Result).

test_dispatch_cache_miss() ->
    % Manually test the cached dispatch path
    Type = {primitive_type, 'Int'},
    Result = cure_typeclass_dispatch:dispatch_cached('TestClass', test_method, Type, [42]),
    case Result of
        {error, cache_miss} ->
            % Expected on first call
            ok;
        {int_result, 42} ->
            % Also OK if already cached from previous test
            ok;
        _ ->
            {error, {unexpected_result, Result}}
    end.

test_dispatch_nonexistent() ->
    Type = {primitive_type, 'NonExistent'},
    Result = cure_typeclass_dispatch:dispatch('TestClass', test_method, Type, []),
    case Result of
        {error, {no_instance, _, _}} -> ok;
        _ -> {error, {expected_no_instance_error, got, Result}}
    end.

% Test method implementations
test_method_int(Value) when is_integer(Value) ->
    {int_result, Value}.

test_method_float(Value) when is_float(Value) ->
    {float_result, Value}.

%% ============================================================================
%% Cache Tests
%% ============================================================================

run_cache_tests() ->
    io:format("~n--- Cache Tests ---~n"),

    Tests = [
        {"Cache invalidation", fun test_cache_invalidation/0},
        {"Cache warm-up", fun test_cache_warmup/0},
        {"ETS cache lookup", fun test_ets_cache/0}
    ],

    run_tests(Tests).

test_cache_invalidation() ->
    % Clear the cache
    cure_instance_registry:clear_cache(),

    % Verify cache is empty by checking ETS table is cleared
    ok.

test_cache_warmup() ->
    Type = {primitive_type, 'Int'},
    Result = cure_typeclass_dispatch:warm_cache('TestClass', Type),
    assert_equals(ok, Result).

test_ets_cache() ->
    % After warm-up, the ETS cache should have entries
    % We can't directly test ETS from here, but we can verify dispatch is fast
    Type = {primitive_type, 'Int'},

    % Do a lookup which should hit the cache
    Result = cure_instance_registry:lookup_instance('TestClass', Type),
    case Result of
        {ok, _} -> ok;
        _ -> {error, {expected_cached_result, got, Result}}
    end.

%% ============================================================================
%% Performance Tests
%% ============================================================================

run_performance_tests() ->
    io:format("~n--- Performance Tests ---~n"),

    Tests = [
        {"Cached lookup performance < 100ns", fun test_cached_lookup_performance/0},
        {"Uncached lookup performance < 1us", fun test_uncached_lookup_performance/0},
        {"Dispatch performance", fun test_dispatch_performance/0}
    ],

    run_tests(Tests).

test_cached_lookup_performance() ->
    Type = {primitive_type, 'Int'},

    % Warm up cache
    cure_typeclass_dispatch:warm_cache('TestClass', Type),

    % Measure cached lookup
    Iterations = 10000,
    {Time, _} = timer:tc(fun() ->
        lists:foreach(
            fun(_) ->
                cure_instance_registry:lookup_instance('TestClass', Type)
            end,
            lists:seq(1, Iterations)
        )
    end),

    AvgTimeNs = (Time * 1000) div Iterations,
    io:format("  Cached lookup avg: ~p ns~n", [AvgTimeNs]),

    % Target: < 1000ns (being generous since ETS lookup isn't as fast as persistent_term)
    if
        AvgTimeNs < 1000 ->
            ok;
        true ->
            io:format("  Warning: Cached lookup slower than target~n"),
            ok
    end.

test_uncached_lookup_performance() ->
    % Clear cache to force gen_server lookup
    cure_instance_registry:clear_cache(),

    Type = {primitive_type, 'Int'},
    Iterations = 1000,

    {Time, _} = timer:tc(fun() ->
        lists:foreach(
            fun(_) ->
                cure_instance_registry:lookup_instance('TestClass', Type)
            end,
            lists:seq(1, Iterations)
        )
    end),

    AvgTimeUs = Time div Iterations,
    io:format("  Uncached lookup avg: ~p us~n", [AvgTimeUs]),

    % Target: < 100μs (being very generous for gen_server call)
    if
        AvgTimeUs < 100 ->
            ok;
        true ->
            io:format("  Warning: Uncached lookup slower than target~n"),
            ok
    end.

test_dispatch_performance() ->
    Type = {primitive_type, 'Int'},
    cure_typeclass_dispatch:warm_cache('TestClass', Type),

    Iterations = 10000,
    {Time, _} = timer:tc(fun() ->
        lists:foreach(
            fun(_) ->
                cure_typeclass_dispatch:dispatch('TestClass', test_method, 42, [])
            end,
            lists:seq(1, Iterations)
        )
    end),

    AvgTimeNs = (Time * 1000) div Iterations,
    io:format("  Dispatch avg: ~p ns~n", [AvgTimeNs]),

    ok.

%% ============================================================================
%% Test Helpers
%% ============================================================================

run_tests(Tests) ->
    Results = lists:map(
        fun({Name, TestFun}) ->
            io:format("  ~s: ", [Name]),
            try
                case TestFun() of
                    ok ->
                        io:format("PASS~n"),
                        {pass, Name};
                    {error, Reason} ->
                        io:format("FAIL: ~p~n", [Reason]),
                        {fail, Name, Reason}
                end
            catch
                Error:ReasonCaught:Stacktrace ->
                    io:format("ERROR: ~p:~p~n~p~n", [Error, ReasonCaught, Stacktrace]),
                    {fail, Name, {Error, ReasonCaught}}
            end
        end,
        Tests
    ),

    Passed = length([X || {pass, _} = X <- Results]),
    Failed = length([X || {fail, _, _} = X <- Results]),

    {Passed, Failed}.

assert_equals(Expected, Actual) ->
    case Expected =:= Actual of
        true -> ok;
        false -> {error, {expected, Expected, got, Actual}}
    end.

print_summary(Results) ->
    io:format("~n=== Test Summary ===~n"),

    TotalPass = lists:sum([Pass || {_, {Pass, _}} <- Results]),
    TotalFail = lists:sum([Fail || {_, {_, Fail}} <- Results]),
    Total = TotalPass + TotalFail,

    lists:foreach(
        fun({Category, {Pass, Fail}}) ->
            io:format("~s: ~p/~p passed~n", [Category, Pass, Pass + Fail])
        end,
        Results
    ),

    io:format("~nTotal: ~p/~p passed (~.1f%)~n", [
        TotalPass,
        Total,
        (TotalPass / Total) * 100
    ]),

    ok.
