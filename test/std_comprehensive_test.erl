%% Cure Standard Library Comprehensive Test Suite
%% Main test runner for all standard library module tests
%% Integrates tests for Std.Core, Std.IO, Std.List, Std.Math, Std.String
-module(std_comprehensive_test).

-export([run/0, run_individual/1, run_with_timing/0]).

-include_lib("eunit/include/eunit.hrl").

%% Main test runner - executes all standard library tests
run() ->
    io:format(
        "~n" ++
            "================================================================================~n" ++
            " CURE STANDARD LIBRARY COMPREHENSIVE TEST SUITE~n" ++
            "================================================================================~n"
    ),

    StartTime = os:timestamp(),

    % Initialize test counters
    put(test_modules, 0),
    put(test_failures, 0),

    % Run all standard library module tests
    TestModules = [
        {std_core_test, "Std.Core - Core functions, comparison, error handling"},
        {std_io_test, "Std.IO - Input/output operations returning Int values"},
        {std_list_test, "Std.List - List operations and transformations"},
        {std_math_test, "Std.Math - Mathematical operations and calculations"},
        {std_string_test, "Std.String - String operations and manipulations"}
    ],

    % Execute each test module
    lists:foreach(
        fun({Module, Description}) ->
            run_test_module(Module, Description)
        end,
        TestModules
    ),

    % Calculate execution time
    EndTime = os:timestamp(),
    ElapsedTime = timer:now_diff(EndTime, StartTime) / 1000000,

    % Print summary
    TotalModules = get(test_modules),
    TotalFailures = get(test_failures),

    io:format(
        "~n" ++
            "================================================================================~n" ++
            " TEST EXECUTION SUMMARY~n" ++
            "================================================================================~n"
    ),

    io:format("Total test modules executed: ~p~n", [TotalModules]),
    io:format("Total execution time: ~.3f seconds~n", [ElapsedTime]),

    if
        TotalFailures == 0 ->
            io:format(
                "~n✅ ALL TESTS PASSED! ✅~n" ++
                    "All ~p standard library test modules completed successfully.~n",
                [TotalModules]
            );
        true ->
            io:format(
                "~n❌ SOME TESTS FAILED! ❌~n" ++
                    "~p out of ~p test modules encountered failures.~n",
                [TotalFailures, TotalModules]
            )
    end,

    io:format(
        "~n" ++
            "================================================================================~n" ++
            " TEST COVERAGE NOTES~n" ++
            "================================================================================~n"
    ),
    print_test_coverage_summary(),

    % Clean up
    erase(test_modules),
    erase(test_failures),

    case TotalFailures of
        0 -> ok;
        _ -> {error, {failed_modules, TotalFailures}}
    end.

%% Run tests with detailed timing information
run_with_timing() ->
    io:format("~n🕐 Running Cure Standard Library tests with detailed timing...~n~n"),

    TestModules = [
        {std_core_test, "Std.Core"},
        {std_io_test, "Std.IO"},
        {std_list_test, "Std.List"},
        {std_math_test, "Std.Math"},
        {std_string_test, "Std.String"}
    ],

    TotalStartTime = os:timestamp(),

    Results = lists:map(
        fun({Module, Name}) ->
            io:format("⏱️  Starting ~s tests...~n", [Name]),
            ModuleStartTime = os:timestamp(),

            Result =
                try
                    Module:run(),
                    {ok, Name}
                catch
                    Error:Reason ->
                        io:format("❌ Error in ~s: ~p:~p~n", [Name, Error, Reason]),
                        {error, {Name, Error, Reason}}
                end,

            ModuleEndTime = os:timestamp(),
            ElapsedTime = timer:now_diff(ModuleEndTime, ModuleStartTime) / 1000000,

            io:format("⏱️  ~s completed in ~.3f seconds~n~n", [Name, ElapsedTime]),

            {Result, ElapsedTime}
        end,
        TestModules
    ),

    TotalEndTime = os:timestamp(),
    TotalElapsedTime = timer:now_diff(TotalEndTime, TotalStartTime) / 1000000,

    % Print timing summary
    io:format("~n📊 TIMING SUMMARY:~n"),
    lists:foreach(
        fun({{Status, Name}, Time}) ->
            StatusIcon =
                case Status of
                    ok -> "✅";
                    {error, _} -> "❌"
                end,
            io:format("  ~s ~s: ~.3f seconds~n", [StatusIcon, Name, Time])
        end,
        Results
    ),

    io:format("~n🏁 Total execution time: ~.3f seconds~n", [TotalElapsedTime]),

    % Count successes and failures
    {Successes, Failures} = lists:foldl(
        fun({{Status, _}, _}, {S, F}) ->
            case Status of
                ok -> {S + 1, F};
                {error, _} -> {S, F + 1}
            end
        end,
        {0, 0},
        Results
    ),

    io:format("📈 Results: ~p passed, ~p failed~n", [Successes, Failures]),

    case Failures of
        0 -> ok;
        _ -> {error, {failed_count, Failures}}
    end.

%% Run an individual test module
run_individual(ModuleName) when is_atom(ModuleName) ->
    io:format("~n🎯 Running individual test module: ~p~n", [ModuleName]),

    case
        lists:member(ModuleName, [
            std_core_test, std_io_test, std_list_test, std_math_test, std_string_test
        ])
    of
        true ->
            StartTime = os:timestamp(),

            Result =
                try
                    ModuleName:run(),
                    io:format("✅ Module ~p completed successfully~n", [ModuleName]),
                    ok
                catch
                    Error:Reason:Stack ->
                        io:format("❌ Module ~p failed: ~p:~p~n", [ModuleName, Error, Reason]),
                        io:format("Stack trace: ~p~n", [Stack]),
                        {error, {Error, Reason}}
                end,

            EndTime = os:timestamp(),
            ElapsedTime = timer:now_diff(EndTime, StartTime) / 1000000,
            io:format("⏱️  Execution time: ~.3f seconds~n", [ElapsedTime]),

            Result;
        false ->
            io:format("❌ Unknown test module: ~p~n", [ModuleName]),
            io:format(
                "Available modules: std_core_test, std_io_test, std_list_test, std_math_test, std_string_test~n"
            ),
            {error, unknown_module}
    end.

%% Internal function to run a test module with error handling
run_test_module(Module, Description) ->
    put(test_modules, get(test_modules) + 1),

    io:format("~n📋 Running: ~s~n", [Description]),
    io:format("   Module: ~p~n", [Module]),

    try
        Module:run(),
        io:format("   Status: ✅ PASSED~n")
    catch
        Error:Reason:Stack ->
            put(test_failures, get(test_failures) + 1),
            io:format("   Status: ❌ FAILED~n"),
            io:format("   Error:  ~p:~p~n", [Error, Reason]),
            io:format("   Stack:  ~p~n", [Stack])
    end.

%% Print test coverage summary
print_test_coverage_summary() ->
    io:format("This test suite covers the following Cure standard library functions:~n~n"),

    io:format("📚 Std.Core:~n"),
    io:format("  • compare/2 - Returns correct Ordering (Lt, Eq, Gt)~n"),
    io:format("  • Boolean operations: not/1, and/2, or/2, xor/2~n"),
    io:format("  • Comparison operations: eq/2, ne/2, lt/2, le/2, gt/2, ge/2~n"),
    io:format("  • Min/max operations: minimum/2, maximum/2, clamp/3~n"),
    io:format("  • Result type operations: ok/1, error/1, map_ok/2, and_then/2~n"),
    io:format("  • Option type operations: some/1, none/0, map_option/2, flat_map_option/2~n"),
    io:format("  • Utility functions: identity/1, compose/2, flip/1, const/1, apply/2, pipe/2~n~n"),

    io:format("🖨️  Std.IO:~n"),
    io:format("  • print/1, println/1 - Confirmed to return Int (0) instead of Unit~n"),
    io:format("  • Type-specific printing: print_int/1, print_float/1, print_bool/1~n"),
    io:format("  • Input operations: read_line/0, read_int/0, read_float/0~n"),
    io:format("  • Debug/error output: debug/1, error/1~n~n"),

    io:format("📝 Std.List:~n"),
    io:format("  • Basic operations: length/1, head/1, tail/1, is_empty/1~n"),
    io:format("  • Construction: cons/2, append/2, reverse/1~n"),
    io:format("  • Transformation: map/2, filter/2, fold_left/3, fold_right/3~n"),
    io:format("  • Access: nth/2, take/2, drop/2~n"),
    io:format("  • Predicates: all/2, any/2, contains/2~n"),
    io:format("  • Safe operations: safe_head/1, safe_tail/1, safe_nth/2~n~n"),

    io:format("🔢 Std.Math:~n"),
    io:format("  • Constants: pi/0, e/0~n"),
    io:format("  • Basic operations: abs/1, sign/1, negate/1~n"),
    io:format("  • Arithmetic: add/2, subtract/2, multiply/2~n"),
    io:format("  • Comparison: min/2, max/2, clamp/3~n"),
    io:format("  • Advanced: power/2, factorial/1, fibonacci/1~n"),
    io:format("  • All functions tested for numerical accuracy~n~n"),

    io:format("🔤 Std.String:~n"),
    io:format("  • Basic operations: length/1, is_empty/1~n"),
    io:format("  • Construction: concat/2, repeat/2~n"),
    io:format("  • Conversion: to_upper/1, to_lower/1~n"),
    io:format("  • Predicates: starts_with/2, ends_with/2~n"),
    io:format("  • Manipulation: trim/1, reverse/1~n"),
    io:format("  • Access: slice/3, take/2, drop/2~n"),
    io:format("  • Note: Many functions currently return placeholder values~n~n"),

    io:format("⚠️  IMPORTANT NOTES:~n"),
    io:format("  • Tests are designed for the current Cure standard library implementation~n"),
    io:format(
        "  • Some functions have placeholder implementations that return simplified values~n"
    ),
    io:format("  • Tests validate both current behavior and expected future behavior~n"),
    io:format("  • All tests use Erlang implementations to simulate Cure function behavior~n"),
    io:format("  • Integration with actual Cure compiler will require minimal changes~n").

%% Utility function to get test statistics
get_test_statistics() ->
    #{
        modules => get(test_modules),
        failures => get(test_failures),
        start_time => get(start_time)
    }.

%% Function to run specific test categories
run_category(Category) ->
    case Category of
        core ->
            run_individual(std_core_test);
        io ->
            run_individual(std_io_test);
        list ->
            run_individual(std_list_test);
        math ->
            run_individual(std_math_test);
        string ->
            run_individual(std_string_test);
        all ->
            run();
        timing ->
            run_with_timing();
        _ ->
            io:format("Unknown category: ~p~n", [Category]),
            io:format("Available categories: core, io, list, math, string, all, timing~n"),
            {error, unknown_category}
    end.

%% Function for quick testing during development
quick_test() ->
    io:format("🚀 Running quick test (core + math only)...~n"),

    try
        std_core_test:run(),
        std_math_test:run(),
        io:format("✅ Quick test completed successfully~n"),
        ok
    catch
        Error:Reason ->
            io:format("❌ Quick test failed: ~p:~p~n", [Error, Reason]),
            {error, {Error, Reason}}
    end.

%% Helper function to validate test module availability
validate_test_modules() ->
    RequiredModules = [std_core_test, std_io_test, std_list_test, std_math_test, std_string_test],

    io:format("🔍 Validating test module availability...~n"),

    Results = lists:map(
        fun(Module) ->
            case code:is_loaded(Module) of
                false ->
                    case code:load_file(Module) of
                        {module, Module} ->
                            io:format("  ✅ ~p: loaded~n", [Module]),
                            {Module, ok};
                        {error, Reason} ->
                            io:format("  ❌ ~p: failed to load (~p)~n", [Module, Reason]),
                            {Module, {error, Reason}}
                    end;
                {file, _} ->
                    io:format("  ✅ ~p: already loaded~n", [Module]),
                    {Module, ok}
            end
        end,
        RequiredModules
    ),

    Failures = [M || {M, {error, _}} <- Results],

    case Failures of
        [] ->
            io:format("✅ All test modules available~n"),
            ok;
        _ ->
            io:format("❌ Missing modules: ~p~n", [Failures]),
            {error, {missing_modules, Failures}}
    end.
