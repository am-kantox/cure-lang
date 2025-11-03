-module(simple_pipe_test).
-export([run/0]).

run() ->
    io:format("~n=== Pipe Operator Result Handling Tests ===~n~n"),

    % Test 1: Bare value |> bare function
    test_bare_to_bare(),

    % Test 2: Bare value |> Result function
    test_bare_to_result_ok(),

    % Test 3: Bare value |> Result function (returns Error)
    test_bare_to_result_error(),

    % Test 4: Chaining bare functions
    test_chain_bare(),

    % Test 5: Error propagation in chain
    test_error_propagation(),

    % Test 6: Mixed bare and Result functions
    test_mixed_chain(),

    io:format("~n=== All tests completed ===~n"),
    halt(0).

test_bare_to_bare() ->
    io:format("Test 1: Bare value |> bare function~n"),
    TransformFun = fun(X) -> X * 2 end,
    Result = cure_std:pipe(5, TransformFun),
    Expected = {'Ok', 10},
    assert_equal(Result, Expected, "5 |> double should return Ok(10)").

test_bare_to_result_ok() ->
    io:format("Test 2: Bare value |> Result function (Ok case)~n"),
    TransformFun = fun(X) -> {'Ok', X * 2} end,
    Result = cure_std:pipe(5, TransformFun),
    Expected = {'Ok', 10},
    assert_equal(Result, Expected, "5 |> ok(double) should return Ok(10)").

test_bare_to_result_error() ->
    io:format("Test 3: Bare value |> Result function (Error case)~n"),
    TransformFun = fun(_X) -> {'Error', "Shit happens"} end,
    Result = cure_std:pipe(5, TransformFun),
    Expected = {'Error', "Shit happens"},
    assert_equal(Result, Expected, "5 |> error(...) should return Error(...)").

test_chain_bare() ->
    io:format("Test 4: Chaining bare functions~n"),
    Double = fun(X) -> X * 2 end,
    Result1 = cure_std:pipe(5, Double),
    Result2 = cure_std:pipe(Result1, Double),
    Expected = {'Ok', 20},
    assert_equal(Result2, Expected, "5 |> double |> double should return Ok(20)").

test_error_propagation() ->
    io:format("Test 5: Error propagation in chain~n"),
    ErrorFun = fun(_X) -> {'Error', "failed"} end,
    Double = fun(X) -> X * 2 end,
    Result1 = cure_std:pipe(5, ErrorFun),
    Result2 = cure_std:pipe(Result1, Double),
    Expected = {'Error', "failed"},
    assert_equal(Result2, Expected, "Error should propagate without calling next function").

test_mixed_chain() ->
    io:format("Test 6: Mixed bare and Result functions~n"),
    Double = fun(X) -> X * 2 end,
    SafeDivide = fun(X) ->
        case X of
            0 -> {'Error', "Cannot divide by zero"};
            _ -> {'Ok', 10 div X}
        end
    end,
    % 5 -> Ok(10)
    Result1 = cure_std:pipe(5, Double),
    % Ok(10) -> Ok(1)
    Result2 = cure_std:pipe(Result1, SafeDivide),
    Expected = {'Ok', 1},
    assert_equal(Result2, Expected, "5 |> double |> safe_divide should return Ok(1)").

assert_equal(Actual, Expected, Message) ->
    case Actual =:= Expected of
        true ->
            io:format("  ✓ PASS: ~s~n", [Message]),
            io:format("    Result: ~p~n", [Actual]);
        false ->
            io:format("  ✗ FAIL: ~s~n", [Message]),
            io:format("    Expected: ~p~n", [Expected]),
            io:format("    Actual:   ~p~n", [Actual]),
            halt(1)
    end.
