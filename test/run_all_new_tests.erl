%% Master Test Runner for New CLI Wrapper and Standard Library Unit Tests
%% This module runs all the newly created unit test suites for the five specified test cases
-module(run_all_new_tests).

-export([run/0]).

%% Run all newly created unit test suites
run() ->
    cure_utils:debug("~n=======================================================~n"),
    cure_utils:debug("Running All New CLI Wrapper and Standard Library Tests~n"),
    cure_utils:debug("=======================================================~n~n"),

    TestResults = [
        run_test_suite("Comprehensive CLI Wrapper Tests", cli_wrapper_comprehensive_test),
        run_test_suite("Cure Wrapper Script Tests", cure_wrapper_script_test),
        run_test_suite("CLI Stdlib Imports Tests", cure_cli_stdlib_imports_test),
        run_test_suite("Stdlib Compilation Failure Tests", stdlib_compilation_failure_test),
        run_test_suite("Std.List.length Function Tests", std_list_length_function_test)
    ],

    cure_utils:debug("~n=======================================================~n"),
    cure_utils:debug("Test Summary~n"),
    cure_utils:debug("=======================================================~n"),

    {Passed, Failed} = lists:foldl(
        fun({Suite, Result}, {PassAcc, FailAcc}) ->
            case Result of
                passed ->
                    cure_utils:debug("✓ ~s: PASSED~n", [Suite]),
                    {PassAcc + 1, FailAcc};
                {failed, Reason} ->
                    cure_utils:debug("✗ ~s: FAILED (~p)~n", [Suite, Reason]),
                    {PassAcc, FailAcc + 1}
            end
        end,
        {0, 0},
        TestResults
    ),

    cure_utils:debug("~nTotal: ~p passed, ~p failed~n", [Passed, Failed]),

    case Failed of
        0 ->
            cure_utils:debug("~nAll CLI wrapper and stdlib tests PASSED! 🎉~n"),
            ok;
        _ ->
            cure_utils:debug("~nSome tests FAILED. Please review the output above.~n"),
            {error, {tests_failed, Failed}}
    end.

%% Run a single test suite and capture the result
run_test_suite(SuiteName, Module) ->
    cure_utils:debug("Running ~s...~n", [SuiteName]),
    try
        Module:run(),
        cure_utils:debug("~s completed successfully.~n~n", [SuiteName]),
        {SuiteName, passed}
    catch
        Error:Reason:Stack ->
            cure_utils:debug("~s FAILED: ~p:~p~n", [SuiteName, Error, Reason]),
            case os:getenv("CURE_DEBUG") of
                "1" -> cure_utils:debug("Stack trace: ~p~n", [Stack]);
                _ -> ok
            end,
            cure_utils:debug("~n"),
            {SuiteName, {failed, {Error, Reason}}}
    end.
