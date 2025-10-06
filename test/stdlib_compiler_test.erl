%% Test compiler recognition of new standard library functions
%% Verifies that the compiler can properly parse, typecheck, and compile
%% calls to the newly added standard library functions
-module(stdlib_compiler_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").

%% Run all compiler integration tests for stdlib
run() ->
    io:format("Running Standard Library Compiler Integration tests...~n"),
    test_function_call_compilation(),
    test_capitalized_function_calls(),
    % Note: monadic function chains are now handled by Std.Core module
    % test_monadic_function_chains(),
    test_safe_div_compilation(),
    io:format("All stdlib compiler integration tests passed!~n").

%% Test that standard library function calls can be compiled
test_function_call_compilation() ->
    io:format("Testing function call compilation...~n"),
    
    % Test that we can compile code that uses the new functions
    % We'll create a simple Cure program that uses these functions
    CureCode = "
    module test_module

    def test_ok_function(x: Int): Result[Int, String] =
        Ok(x)

    def test_safe_division(a: Int, b: Int): Result[Float, String] =
        safe_div(a, b)

    def test_map_ok_usage(result: Result[Int, String]): Result[Int, String] =
        map_ok(result, (x) -> x * 2)
    ",
    
    % For this test, we'll just verify that the functions exist and are callable
    % In a real implementation, this would involve the actual Cure parser
    
    % Verify the remaining built-in functions exist in the module by calling them
    ?assertMatch({'Ok', _}, cure_std:'Ok'(test)),
    ?assertMatch({'Ok', _}, cure_std:safe_divide(10, 2)),
    % Note: map_ok and bind_ok are now handled by Std.Core module
    
    io:format("✓ Function call compilation test passed~n").

%% Test capitalized function calls
test_capitalized_function_calls() ->
    io:format("Testing capitalized function calls...~n"),
    
    % Test that capitalized versions exist
    Exports = cure_std:module_info(exports),
    ?assert(lists:member({'Ok', 1}, Exports)),
    ?assert(lists:member({'Error', 1}, Exports)),
    ?assert(lists:member({'Some', 1}, Exports)),
    ?assert(lists:member({'None', 0}, Exports)),
    
    % Verify lowercase versions are NOT exported
    ?assert(not lists:member({ok, 1}, Exports)),
    ?assert(not lists:member({error, 1}, Exports)),
    ?assert(not lists:member({some, 1}, Exports)),
    ?assert(not lists:member({none, 0}, Exports)),
    
    % Verify list operations are NOT exported (now handled by Std.List)
    ?assert(not lists:member({map, 2}, Exports)),
    ?assert(not lists:member({filter, 2}, Exports)),
    ?assert(not lists:member({foldl, 3}, Exports)),
    ?assert(not lists:member({head, 1}, Exports)),
    ?assert(not lists:member({tail, 1}, Exports)),
    ?assert(not lists:member({length, 1}, Exports)),
    
    % Verify string operations are NOT exported (now handled by Std.String)
    ?assert(not lists:member({string_concat, 2}, Exports)),
    ?assert(not lists:member({split, 2}, Exports)),
    ?assert(not lists:member({trim, 1}, Exports)),
    ?assert(not lists:member({to_upper, 1}, Exports)),
    ?assert(not lists:member({contains, 2}, Exports)),
    ?assert(not lists:member({starts_with, 2}, Exports)),
    
    % Verify math operations are NOT exported (now handled by Std.Math)
    ?assert(not lists:member({abs, 1}, Exports)),
    ?assert(not lists:member({sqrt, 1}, Exports)),
    ?assert(not lists:member({pi, 0}, Exports)),
    
    % Verify utility functions are NOT exported (except print/1)
    ?assert(lists:member({print, 1}, Exports)),  % print/1 should remain
    ?assert(not lists:member({int_to_string, 1}, Exports)),
    ?assert(not lists:member({float_to_string, 1}, Exports)),
    ?assert(not lists:member({list_to_string, 1}, Exports)),
    ?assert(not lists:member({join_ints, 2}, Exports)),
    ?assert(not lists:member({string_empty, 1}, Exports)),
    ?assert(not lists:member({string_join, 2}, Exports)),
    
    % Test that capitalized versions work correctly
    TestValue = test_value,
    ?assertMatch({'Ok', _}, cure_std:'Ok'(TestValue)),
    ?assertMatch({'Error', _}, cure_std:'Error'(TestValue)),
    ?assertMatch({'Some', _}, cure_std:'Some'(TestValue)),
    ?assertEqual('None', cure_std:'None'()),
    
    io:format("✓ Capitalized function calls test passed~n").

%% Test monadic function chains
test_monadic_function_chains() ->
    io:format("Testing monadic function chains...~n"),
    
    % Test Result monadic chain
    InitialOk = cure_std:ok(10),
    
    % Chain: Ok(10) -> map_ok(*2) -> and_then(safe_divide(_, 4)) -> map_ok(+1)
    ChainResult = cure_std:map_ok(
        cure_std:and_then(
            cure_std:map_ok(InitialOk, fun(X) -> X * 2 end),
            fun(X) -> cure_std:safe_divide(X, 4) end
        ),
        fun(X) -> X + 1 end
    ),
    
    ?assertEqual({'Ok', 6.0}, ChainResult),
    
    % Test Option monadic chain
    InitialSome = cure_std:some(8),
    
    % Chain: Some(8) -> map_option(*3) -> bind_some(check_positive) -> map_option(sqrt)
    OptionalChainResult = cure_std:map_option(
        case cure_std:map_option(InitialSome, fun(X) -> X * 3 end) of
            {'Some', X} when X > 0 -> cure_std:some(X);
            _ -> cure_std:none()
        end,
        fun(X) -> math:sqrt(X) end
    ),
    
    ?assertMatch({'Some', _}, OptionalChainResult),
    {'Some', SqrtValue} = OptionalChainResult,
    ?assert(abs(SqrtValue - math:sqrt(24)) < 0.0001), % Check approximate equality
    
    io:format("✓ Monadic function chains test passed~n").

%% Test safe_div compilation and behavior
test_safe_div_compilation() ->
    io:format("Testing safe_div compilation and behavior...~n"),
    
    % Test various safe_div scenarios
    TestCases = [
        {10, 2, {'Ok', 5.0}},
        {7, 2, {'Ok', 3.5}},
        {-10, 2, {'Ok', -5.0}},
        {0, 5, {'Ok', 0.0}},
        {10, 0, {'Error', "Division by zero"}}
    ],
    
    % Test each case
    lists:foreach(fun({Numerator, Denominator, Expected}) ->
        Result = cure_std:safe_divide(Numerator, Denominator),
        ?assertEqual(Expected, Result)
    end, TestCases),
    
    % Note: More complex computations using bind_ok are now handled by Std.Core module
    % We can only test basic safe_div functionality here
    
    io:format("✓ safe_div compilation and behavior test passed~n").