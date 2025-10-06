%% Cure Standard Library Tests
%% Tests for standard library functions including capitalized aliases,
%% monadic operations, and safe mathematical functions
-module(stdlib_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").

%% Run all standard library tests
run() ->
    io:format("Running Cure Standard Library tests...~n"),
    test_capitalized_alias_functions(),
    test_safe_div_function(),
    % Note: monadic operations (map_ok, bind_ok, map_some, bind_some) are now handled by Std.Core module
    % test_result_monadic_operations(),
    % test_option_monadic_operations(),
    test_remaining_functions(),
    io:format("All standard library tests passed!~n").

%% ============================================================================
%% Test 1: Capitalized constructor functions
%% ============================================================================

test_capitalized_alias_functions() ->
    io:format("Testing capitalized constructor functions...~n"),
    
    % Test Ok constructor
    Value1 = 42,
    OkResult1 = cure_stdlib:'Ok'(Value1),
    ?assertEqual({'Ok', 42}, OkResult1),
    
    % Test Error constructor
    Reason1 = "something went wrong",
    ErrorResult1 = cure_stdlib:'Error'(Reason1),
    ?assertEqual({'Error', "something went wrong"}, ErrorResult1),
    
    % Test Some constructor
    Value2 = "hello",
    SomeResult1 = cure_stdlib:'Some'(Value2),
    ?assertEqual({'Some', "hello"}, SomeResult1),
    
    % Test None constructor
    NoneResult1 = cure_stdlib:'None'(),
    ?assertEqual('None', NoneResult1),
    
    io:format("✓ Capitalized constructor functions test passed~n").

%% ============================================================================
%% Test 2: safe_div function
%% ============================================================================

test_safe_div_function() ->
    io:format("Testing safe_div function...~n"),
    
    % Test division by zero - should return Error
    DivByZeroResult = cure_stdlib:safe_div(10, 0),
    ?assertMatch({'Error', "Division by zero"}, DivByZeroResult),
    
    % Test valid division - should return Ok with result
    ValidDivResult1 = cure_stdlib:safe_div(10, 2),
    ?assertMatch({'Ok', 5.0}, ValidDivResult1),
    
    % Test division with float result
    ValidDivResult2 = cure_stdlib:safe_div(7, 2),
    ?assertMatch({'Ok', 3.5}, ValidDivResult2),
    
    % Test division with negative numbers
    ValidDivResult3 = cure_stdlib:safe_div(-10, 2),
    ?assertMatch({'Ok', -5.0}, ValidDivResult3),
    
    % Test division of zero by non-zero
    ValidDivResult4 = cure_stdlib:safe_div(0, 5),
    ?assertMatch({'Ok', 0.0}, ValidDivResult4),
    
    io:format("✓ safe_div function test passed~n").

%% ============================================================================
%% Test 3: Result monadic operations (map_ok and bind_ok)
%% ============================================================================

test_result_monadic_operations() ->
    io:format("Testing Result monadic operations...~n"),
    
    % Test map_ok with Ok value - should apply function
    OkValue = cure_stdlib:ok(5),
    DoubleOkResult = cure_stdlib:map_ok(OkValue, fun(X) -> X * 2 end),
    ?assertEqual({'Ok', 10}, DoubleOkResult),
    
    % Test map_ok with Error value - should propagate Error
    ErrorValue = cure_stdlib:error("failed"),
    DoubleErrorResult = cure_stdlib:map_ok(ErrorValue, fun(X) -> X * 2 end),
    ?assertEqual({'Error', "failed"}, DoubleErrorResult),
    
    % Test bind_ok with Ok value - should apply function and flatten
    OkValue2 = cure_stdlib:ok(4),
    SafeSqrtResult = cure_stdlib:bind_ok(OkValue2, fun(X) -> 
        cure_stdlib:ok(math:sqrt(X))
    end),
    ?assertEqual({'Ok', 2.0}, SafeSqrtResult),
    
    % Test bind_ok with Error value - should propagate Error
    ErrorValue2 = cure_stdlib:error("invalid input"),
    SafeSqrtErrorResult = cure_stdlib:bind_ok(ErrorValue2, fun(X) ->
        cure_stdlib:ok(math:sqrt(X))
    end),
    ?assertEqual({'Error', "invalid input"}, SafeSqrtErrorResult),
    
    % Test bind_ok with function that returns Error
    OkValue3 = cure_stdlib:ok(-1),
    NegativeSqrtResult = cure_stdlib:bind_ok(OkValue3, fun(X) ->
        if 
            X < 0 -> cure_stdlib:error("negative number");
            true -> cure_stdlib:ok(math:sqrt(X))
        end
    end),
    ?assertEqual({'Error', "negative number"}, NegativeSqrtResult),
    
    % Test chaining operations
    ChainResult = cure_stdlib:bind_ok(
        cure_stdlib:safe_div(10, 2),
        fun(X) -> cure_stdlib:map_ok(cure_stdlib:ok(X), fun(Y) -> Y + 3 end) end
    ),
    ?assertEqual({'Ok', 8.0}, ChainResult),
    
    io:format("✓ Result monadic operations test passed~n").

%% ============================================================================
%% Test 4: Option monadic operations (map_some and bind_some)
%% ============================================================================

test_option_monadic_operations() ->
    io:format("Testing Option monadic operations...~n"),
    
    % Test map_some with Some value - should apply function
    SomeValue = cure_stdlib:some(10),
    TripleSomeResult = cure_stdlib:map_some(SomeValue, fun(X) -> X * 3 end),
    ?assertEqual({'Some', 30}, TripleSomeResult),
    
    % Test map_some with None value - should propagate None
    NoneValue = cure_stdlib:none(),
    TripleNoneResult = cure_stdlib:map_some(NoneValue, fun(X) -> X * 3 end),
    ?assertEqual('None', TripleNoneResult),
    
    % Test bind_some with Some value - should apply function and flatten
    SomeValue2 = cure_stdlib:some(16),
    MaybeSqrtResult = cure_stdlib:bind_some(SomeValue2, fun(X) ->
        if 
            X >= 0 -> cure_stdlib:some(math:sqrt(X));
            true -> cure_stdlib:none()
        end
    end),
    ?assertEqual({'Some', 4.0}, MaybeSqrtResult),
    
    % Test bind_some with None value - should propagate None
    NoneValue2 = cure_stdlib:none(),
    MaybeSqrtNoneResult = cure_stdlib:bind_some(NoneValue2, fun(X) ->
        cure_stdlib:some(math:sqrt(X))
    end),
    ?assertEqual('None', MaybeSqrtNoneResult),
    
    % Test bind_some with function that returns None
    SomeValue3 = cure_stdlib:some(-5),
    NegativeSqrtOptionResult = cure_stdlib:bind_some(SomeValue3, fun(X) ->
        if 
            X >= 0 -> cure_stdlib:some(math:sqrt(X));
            true -> cure_stdlib:none()
        end
    end),
    ?assertEqual('None', NegativeSqrtOptionResult),
    
    % Test chaining option operations
    ChainOptionResult = cure_stdlib:bind_some(
        cure_stdlib:some(25),
        fun(X) -> 
            cure_stdlib:map_some(cure_stdlib:some(math:sqrt(X)), fun(Y) -> Y + 2 end)
        end
    ),
    ?assertEqual({'Some', 7.0}, ChainOptionResult),
    
    io:format("✓ Option monadic operations test passed~n").

%% ============================================================================
%% Test 5: Test remaining functions work correctly
%% ============================================================================

test_remaining_functions() ->
    io:format("Testing remaining built-in functions...~n"),
    
    % Test capitalized constructor functions (these remain as built-ins)
    ?assertMatch({'Ok', _}, cure_stdlib:'Ok'(test_value)),
    ?assertMatch({'Error', _}, cure_stdlib:'Error'(test_error)),
    ?assertMatch({'Some', _}, cure_stdlib:'Some'(test_value)),
    ?assertEqual('None', cure_stdlib:'None'()),
    
    % Test basic constructor functions
    TestOk = cure_stdlib:'Ok'(42),
    TestSome = cure_stdlib:'Some'(42),
    TestError = cure_stdlib:'Error'("test"),
    TestNone = cure_stdlib:'None'(),
    
    % Verify basic functions work
    ?assertMatch({'Ok', 42}, TestOk),
    ?assertMatch({'Some', 42}, TestSome),
    ?assertMatch({'Error', "test"}, TestError),
    ?assertEqual('None', TestNone),
    
    % Verify safe_div function is still callable
    ?assertMatch({'Ok', _}, cure_stdlib:safe_div(10, 2)),
    ?assertMatch({'Error', _}, cure_stdlib:safe_div(10, 0)),
    
    % Note: List operations (map, filter, foldl, head, tail, length) are now handled by Std.List module
    
    % Note: String operations (string_concat, split, trim, to_upper, contains, starts_with) are now handled by Std.String module
    
    io:format("✓ Remaining built-in functions test passed~n").
