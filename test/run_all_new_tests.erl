%% Master Test Runner for New CLI Wrapper and Standard Library Unit Tests
%% This module runs all the newly created unit test suites for the five specified test cases
-module(run_all_new_tests).

-export([run/0]).

%% Run all newly created unit test suites
run() ->
    io:format("~n=======================================================~n"),
    io:format("Running All New CLI Wrapper and Standard Library Tests~n"),
    io:format("=======================================================~n~n"),

    TestResults = [
        run_test_suite("Comprehensive CLI Wrapper Tests", cli_wrapper_comprehensive_test),
        run_test_suite("Cure Wrapper Script Tests", cure_wrapper_script_test),
        run_test_suite("CLI Stdlib Imports Tests", cure_cli_stdlib_imports_test),
        run_test_suite("Stdlib Compilation Failure Tests", stdlib_compilation_failure_test),
        run_test_suite("Std.List.length Function Tests", std_list_length_function_test)
    ],

    io:format("~n=======================================================~n"),
    io:format("Test Summary~n"),
    io:format("=======================================================~n"),

    {Passed, Failed} = lists:foldl(
        fun({Suite, Result}, {PassAcc, FailAcc}) ->
            case Result of
                passed ->
                    io:format("✓ ~s: PASSED~n", [Suite]),
                    {PassAcc + 1, FailAcc};
                {failed, Reason} ->
                    io:format("✗ ~s: FAILED (~p)~n", [Suite, Reason]),
                    {PassAcc, FailAcc + 1}
            end
        end,
        {0, 0},
        TestResults
    ),

    io:format("~nTotal: ~p passed, ~p failed~n", [Passed, Failed]),

    case Failed of
        0 ->
            io:format("~nAll CLI wrapper and stdlib tests PASSED! 🎉~n"),
            ok;
        _ ->
            io:format("~nSome tests FAILED. Please review the output above.~n"),
            {error, {tests_failed, Failed}}
    end.

%% Run a single test suite and capture the result
run_test_suite(SuiteName, Module) ->
    io:format("Running ~s...~n", [SuiteName]),
    try
        Module:run(),
        io:format("~s completed successfully.~n~n", [SuiteName]),
        {SuiteName, passed}
    catch
        Error:Reason:Stack ->
            io:format("~s FAILED: ~p:~p~n", [SuiteName, Error, Reason]),
            case os:getenv("CURE_DEBUG") of
                "1" -> io:format("Stack trace: ~p~n", [Stack]);
                _ -> ok
            end,
            io:format("~n"),
            {SuiteName, {failed, {Error, Reason}}}
    end.
