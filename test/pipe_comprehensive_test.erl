-module(pipe_comprehensive_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").

run() ->
    io:format("~n=== Comprehensive Pipe Operator Test ===~n~n"),

    Tests = [
        {"1. Parse simple pipe", fun test_parse_simple/0},
        {"2. Parse pipe chain", fun test_parse_chain/0},
        {"3. Parse pipe with args", fun test_parse_with_args/0},
        {"4. Verify AST structure", fun test_ast_structure/0},
        {"5. Runtime behavior", fun test_runtime/0}
    ],

    Results = lists:map(
        fun({Name, TestFun}) ->
            io:format("Testing: ~s~n", [Name]),
            try
                case TestFun() of
                    ok ->
                        io:format("  ✓ PASS~n"),
                        {ok, Name};
                    {error, Reason} ->
                        io:format("  ✗ FAIL: ~p~n", [Reason]),
                        {error, Name, Reason}
                end
            catch
                Class:Error:Stack ->
                    io:format("  ✗ EXCEPTION: ~p:~p~n", [Class, Error]),
                    io:format("    Stack: ~p~n", [Stack]),
                    {exception, Name, {Class, Error}}
            end
        end,
        Tests
    ),

    Passed = length([X || {ok, _} = X <- Results]),
    Failed = length(Results) - Passed,

    io:format("~n=== Summary ===~n"),
    io:format("Total: ~p, Passed: ~p, Failed: ~p~n", [length(Results), Passed, Failed]),

    case Failed of
        0 ->
            io:format("~n✓ All tests passed!~n"),
            halt(0);
        _ ->
            io:format("~n✗ Some tests failed!~n"),
            halt(1)
    end.

test_parse_simple() ->
    {ok, AST} = cure_parser:parse_file("examples/simple_pipe_test.cure"),
    case AST of
        [_Module | _] -> ok;
        _ -> {error, {unexpected_ast, AST}}
    end.

test_parse_chain() ->
    {ok, [Module]} = cure_parser:parse_file("examples/simple_pipe_test.cure"),
    #module_def{name = 'SimplePipeTest', items = Functions} = Module,
    case lists:keyfind(test2, 2, Functions) of
        false ->
            {error, test2_not_found};
        #function_def{body = Body} ->
            % Should have nested pipe operators
            case has_pipe_operator(Body) of
                true -> ok;
                false -> {error, no_pipe_in_test2}
            end
    end.

test_parse_with_args() ->
    {ok, [Module]} = cure_parser:parse_file("examples/simple_pipe_test.cure"),
    #module_def{name = 'SimplePipeTest', items = Functions} = Module,
    case lists:keyfind(test3, 2, Functions) of
        false ->
            {error, test3_not_found};
        #function_def{body = Body} ->
            % Should have pipe with function call
            case has_pipe_operator(Body) of
                true -> ok;
                false -> {error, no_pipe_in_test3}
            end
    end.

test_ast_structure() ->
    {ok, [Module]} = cure_parser:parse_file("examples/simple_pipe_test.cure"),
    #module_def{name = 'SimplePipeTest', items = Functions} = Module,
    case lists:keyfind(test1, 2, Functions) of
        false ->
            {error, test1_not_found};
        #function_def{body = Body} ->
            % Verify it's a binary_op_expr with |>
            case Body of
                #binary_op_expr{op = '|>', left = Left, right = Right} ->
                    % Left should be literal 5
                    case Left of
                        #literal_expr{value = 5} ->
                            % Right should be identifier double
                            case Right of
                                #identifier_expr{name = double} -> ok;
                                _ -> {error, {unexpected_right, Right}}
                            end;
                        _ ->
                            {error, {unexpected_left, Left}}
                    end;
                _ ->
                    {error, {not_binary_op, Body}}
            end
    end.

test_runtime() ->
    % Test runtime semantics
    Tests = [
        % Bare value |> bare function = Ok(result)
        {5, fun(X) -> X * 2 end, {'Ok', 10}},
        % Ok value |> bare function = Ok(result)
        {{'Ok', 5}, fun(X) -> X * 2 end, {'Ok', 10}},
        % Error |> function = Error (function not called)
        {{'Error', reason}, fun(_) -> throw(should_not_be_called) end, {'Error', reason}},
        % Bare value |> Result function = Result
        {5, fun(X) -> {'Ok', X * 2} end, {'Ok', 10}}
    ],

    Results = lists:map(
        fun({Input, Fun, Expected}) ->
            Result = cure_std:pipe(Input, Fun),
            case Result =:= Expected of
                true -> ok;
                false -> {error, {expected, Expected, got, Result}}
            end
        end,
        Tests
    ),

    case lists:all(fun(R) -> R =:= ok end, Results) of
        true -> ok;
        false -> hd([R || R <- Results, R =/= ok])
    end.

% Helper to check if expression contains pipe operator
has_pipe_operator(#binary_op_expr{op = '|>'}) ->
    true;
has_pipe_operator(#binary_op_expr{left = Left, right = Right}) ->
    has_pipe_operator(Left) orelse has_pipe_operator(Right);
has_pipe_operator(_) ->
    false.
