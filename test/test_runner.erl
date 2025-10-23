%% Test Runner - Runs all working Cure compiler tests
-module(test_runner).

-export([run_all/0, run_basic/0, run_integration/0, run_performance/0]).

%% Run all available tests (basic + integration)
run_all() ->
    cure_utils:debug("========================================~n"),
    cure_utils:debug("Cure Compiler Complete Test Suite~n"),
    cure_utils:debug("========================================~n"),

    % Run basic tests first
    BasicResult = run_basic_tests(),

    % Run integration tests
    IntegrationResult = run_integration_tests(),

    % Summarize all results
    case {BasicResult, IntegrationResult} of
        {ok, ok} ->
            cure_utils:debug("~n🎉 ALL TEST SUITES PASSED! 🎉~n"),
            ok;
        _ ->
            cure_utils:debug("~n❌ Some test suites failed~n"),
            error
    end.

%% Run only basic tests
run_basic() ->
    run_basic_tests().

%% Run only integration tests
run_integration() ->
    run_integration_tests().

%% Run performance tests
run_performance() ->
    cure_utils:debug("========================================~n"),
    cure_utils:debug("Cure Compiler Performance Tests~n"),
    cure_utils:debug("========================================~n"),

    try
        performance_simple_test:run()
    catch
        Error:Reason:Stack ->
            cure_utils:debug("❌ Performance test suite FAILED~n"),
            cure_utils:debug("Error: ~p:~p~n", [Error, Reason]),
            cure_utils:debug("Stack: ~p~n", [Stack]),
            error
    end.

%% Run basic test suites
run_basic_tests() ->
    Tests = [
        {fsm_simple_test, "FSM Runtime System"},
        {types_simple_test, "Type System & Inference"},
        {codegen_simple_test, "Code Generation & BEAM"},
        {cli_output_test, "CLI Output Messages"}
    ],

    Results = lists:map(fun run_test_suite/1, Tests),

    cure_utils:debug("~n----------------------------------------~n"),
    cure_utils:debug("Basic Test Summary~n"),
    cure_utils:debug("----------------------------------------~n"),

    Passed = length([ok || ok <- Results]),
    Total = length(Results),
    Failed = Total - Passed,

    cure_utils:debug("Basic test suites: ~w~n", [Total]),
    cure_utils:debug("Passed: ~w~n", [Passed]),
    cure_utils:debug("Failed: ~w~n", [Failed]),

    case Failed of
        0 ->
            cure_utils:debug("✓ All basic tests passed!~n"),
            ok;
        _ ->
            cure_utils:debug("❌ Some basic tests failed~n"),
            error
    end.

%% Run integration test suites
run_integration_tests() ->
    cure_utils:debug("~n========================================~n"),
    cure_utils:debug("Integration Tests~n"),
    cure_utils:debug("========================================~n"),

    try
        integration_simple_test:run()
    catch
        Error:Reason:Stack ->
            cure_utils:debug("❌ Integration test suite FAILED~n"),
            cure_utils:debug("Error: ~p:~p~n", [Error, Reason]),
            cure_utils:debug("Stack: ~p~n", [Stack]),
            error
    end.

%% Run a single test suite
run_test_suite({Module, Description}) ->
    cure_utils:debug("~n[~s]~n", [Description]),
    cure_utils:debug("----------------------------------------~n"),

    try
        Module:run(),
        ok
    catch
        Error:Reason:Stack ->
            cure_utils:debug("❌ Test suite ~w FAILED~n", [Module]),
            cure_utils:debug("Error: ~p:~p~n", [Error, Reason]),
            cure_utils:debug("Stack: ~p~n", [Stack]),
            error
    end.
