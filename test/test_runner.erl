%% Test Runner - Runs all working Cure compiler tests
-module(test_runner).

-export([run_all/0, run_basic/0, run_integration/0, run_performance/0]).

%% Run all available tests (basic + integration)
run_all() ->
    io:format("========================================~n"),
    io:format("Cure Compiler Complete Test Suite~n"),
    io:format("========================================~n"),
    
    % Run basic tests first
    BasicResult = run_basic_tests(),
    
    % Run integration tests
    IntegrationResult = run_integration_tests(),
    
    % Summarize all results
    case {BasicResult, IntegrationResult} of
        {ok, ok} ->
            io:format("~n🎉 ALL TEST SUITES PASSED! 🎉~n"),
            ok;
        _ ->
            io:format("~n❌ Some test suites failed~n"),
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
    io:format("========================================~n"),
    io:format("Cure Compiler Performance Tests~n"),
    io:format("========================================~n"),
    
    try
        performance_simple_test:run()
    catch
        Error:Reason:Stack ->
            io:format("❌ Performance test suite FAILED~n"),
            io:format("Error: ~p:~p~n", [Error, Reason]),
            io:format("Stack: ~p~n", [Stack]),
            error
    end.

%% Run basic test suites
run_basic_tests() ->
    Tests = [
        {fsm_simple_test, "FSM Runtime System"},
        {types_simple_test, "Type System & Inference"},
        {codegen_simple_test, "Code Generation & BEAM"}
    ],
    
    Results = lists:map(fun run_test_suite/1, Tests),
    
    io:format("~n----------------------------------------~n"),
    io:format("Basic Test Summary~n"),
    io:format("----------------------------------------~n"),
    
    Passed = length([ok || ok <- Results]),
    Total = length(Results),
    Failed = Total - Passed,
    
    io:format("Basic test suites: ~w~n", [Total]),
    io:format("Passed: ~w~n", [Passed]),
    io:format("Failed: ~w~n", [Failed]),
    
    case Failed of
        0 -> 
            io:format("✓ All basic tests passed!~n"),
            ok;
        _ -> 
            io:format("❌ Some basic tests failed~n"),
            error
    end.

%% Run integration test suites  
run_integration_tests() ->
    io:format("~n========================================~n"),
    io:format("Integration Tests~n"),
    io:format("========================================~n"),
    
    try
        integration_simple_test:run()
    catch
        Error:Reason:Stack ->
            io:format("❌ Integration test suite FAILED~n"),
            io:format("Error: ~p:~p~n", [Error, Reason]),
            io:format("Stack: ~p~n", [Stack]),
            error
    end.

%% Run a single test suite
run_test_suite({Module, Description}) ->
    io:format("~n[~s]~n", [Description]),
    io:format("----------------------------------------~n"),
    
    try
        Module:run(),
        ok
    catch
        Error:Reason:Stack ->
            io:format("❌ Test suite ~w FAILED~n", [Module]),
            io:format("Error: ~p:~p~n", [Error, Reason]),
            io:format("Stack: ~p~n", [Stack]),
            error
    end.