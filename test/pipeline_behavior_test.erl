%% Comprehensive Test Suite for Pipeline Behavior
%% Tests the three rules specified for the pipe operator:
%% 1. If LHO is error(reason), propagate it
%% 2. If LHO is ok(value), unwrap and pass to RHO, wrapping result unless already a monad  
%% 3. If LHO is neither ok() nor error(), pass to RHO and wrap unless already a monad

-module(pipeline_behavior_test).
-include_lib("eunit/include/eunit.hrl").

%% Test Rule 1: Error propagation
rule1_error_propagation_test() ->
    ErrorValue = {'Error', "Test error"},
    TestFunction = fun(X) -> X * 2 end,
    
    % Test direct pipe call
    Result = cure_std:pipe(ErrorValue, TestFunction),
    ?assertEqual(ErrorValue, Result).

%% Test Rule 2: Ok value unwrapping and wrapping
rule2_ok_unwrapping_basic_test() ->
    OkValue = {'Ok', 10},
    DoubleFunction = fun(X) -> X * 2 end,
    
    Result = cure_std:pipe(OkValue, DoubleFunction),
    ?assertEqual({'Ok', 20}, Result).

rule2_ok_unwrapping_with_monad_result_test() ->
    OkValue = {'Ok', 10},
    MonadFunction = fun(X) -> 
        if X > 5 -> {'Ok', X * 2};
           true -> {'Error', "Value too small"}
        end 
    end,
    
    Result = cure_std:pipe(OkValue, MonadFunction),
    ?assertEqual({'Ok', 20}, Result).

rule2_ok_unwrapping_with_error_result_test() ->
    OkValue = {'Ok', 3},
    MonadFunction = fun(X) -> 
        if X > 5 -> {'Ok', X * 2};
           true -> {'Error', "Value too small"}
        end 
    end,
    
    Result = cure_std:pipe(OkValue, MonadFunction),
    ?assertEqual({'Error', "Value too small"}, Result).

%% Test Rule 3: Non-monad value handling
rule3_non_monad_basic_test() ->
    PlainValue = 15,
    DoubleFunction = fun(X) -> X * 2 end,
    
    Result = cure_std:pipe(PlainValue, DoubleFunction),
    ?assertEqual({'Ok', 30}, Result).

rule3_non_monad_with_monad_result_test() ->
    PlainValue = 15,
    MonadFunction = fun(X) -> 
        if X > 10 -> {'Ok', X * 2};
           true -> {'Error', "Value too small"}
        end 
    end,
    
    Result = cure_std:pipe(PlainValue, MonadFunction),
    ?assertEqual({'Ok', 30}, Result).

rule3_non_monad_with_error_result_test() ->
    PlainValue = 5,
    MonadFunction = fun(X) -> 
        if X > 10 -> {'Ok', X * 2};
           true -> {'Error', "Value too small"}
        end 
    end,
    
    Result = cure_std:pipe(PlainValue, MonadFunction),
    ?assertEqual({'Error', "Value too small"}, Result).

%% Test chaining behavior
chaining_ok_to_ok_test() ->
    AddTen = fun(X) -> X + 10 end,
    MultiplyTwo = fun(X) -> X * 2 end,
    
    % Chain: ok(5) -> AddTen -> MultiplyTwo
    Result1 = cure_std:pipe({'Ok', 5}, AddTen),
    Result2 = cure_std:pipe(Result1, MultiplyTwo),
    
    ?assertEqual({'Ok', 15}, Result1),
    ?assertEqual({'Ok', 30}, Result2).

chaining_with_error_propagation_test() ->
    AddTen = fun(X) -> X + 10 end,
    ErrorFunction = fun(_X) -> {'Error', "Deliberate error"} end,
    MultiplyTwo = fun(X) -> X * 2 end,
    
    % Chain: ok(5) -> AddTen -> ErrorFunction -> MultiplyTwo
    Result1 = cure_std:pipe({'Ok', 5}, AddTen),
    Result2 = cure_std:pipe(Result1, ErrorFunction), 
    Result3 = cure_std:pipe(Result2, MultiplyTwo),
    
    ?assertEqual({'Ok', 15}, Result1),
    ?assertEqual({'Error', "Deliberate error"}, Result2),
    ?assertEqual({'Error', "Deliberate error"}, Result3).

%% Test edge cases
edge_case_function_throws_exception_test() ->
    ThrowingFunction = fun(_X) -> throw(deliberate_exception) end,
    
    Result = cure_std:pipe({'Ok', 5}, ThrowingFunction),
    ?assertMatch({'Error', {pipe_runtime_error, throw, deliberate_exception}}, Result).

edge_case_function_raises_error_test() ->
    ErrorFunction = fun(_X) -> error(deliberate_error) end,
    
    Result = cure_std:pipe({'Ok', 5}, ErrorFunction),
    ?assertMatch({'Error', {pipe_runtime_error, error, deliberate_error}}, Result).

%% Test monad detection utility
is_monad_test() ->
    ?assertEqual(true, cure_std:is_monad({'Ok', 42})),
    ?assertEqual(true, cure_std:is_monad({'Error', "test error"})),
    ?assertEqual(false, cure_std:is_monad(42)),
    ?assertEqual(false, cure_std:is_monad("hello")),
    ?assertEqual(false, cure_std:is_monad([1, 2, 3])).

%% Test complex chaining scenario
complex_chaining_scenario_test() ->
    % Define some test functions
    SafeDivide = fun({Numerator, Denominator}) ->
        case Denominator of
            0 -> {'Error', "Division by zero"};
            _ -> {'Ok', Numerator / Denominator}
        end
    end,
    
    MultiplyBy10 = fun(X) -> X * 10 end,
    
    CheckPositive = fun(X) ->
        if X > 0 -> {'Ok', X};
           true -> {'Error', "Negative result"}
        end
    end,
    
    % Test successful chain: {10, 2} -> SafeDivide -> MultiplyBy10 -> CheckPositive
    Result1 = cure_std:pipe({10, 2}, SafeDivide),
    Result2 = cure_std:pipe(Result1, MultiplyBy10),
    Result3 = cure_std:pipe(Result2, CheckPositive),
    
    ?assertEqual({'Ok', 5.0}, Result1),
    ?assertEqual({'Ok', 50.0}, Result2),
    ?assertEqual({'Ok', 50.0}, Result3),
    
    % Test chain with error: {10, 0} -> SafeDivide -> MultiplyBy10 -> CheckPositive
    Error1 = cure_std:pipe({10, 0}, SafeDivide),
    Error2 = cure_std:pipe(Error1, MultiplyBy10),
    Error3 = cure_std:pipe(Error2, CheckPositive),
    
    ?assertEqual({'Error', "Division by zero"}, Error1),
    ?assertEqual({'Error', "Division by zero"}, Error2),
    ?assertEqual({'Error', "Division by zero"}, Error3).