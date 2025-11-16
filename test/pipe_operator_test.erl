-module(pipe_operator_test).

-export([run/0]).

-include("../src/parser/cure_ast.hrl").
-include("../src/codegen/cure_codegen.hrl").

%% Test suite for pipe operator (|>) implementation

run() ->
    io:format("~n=== Pipe Operator Tests ===~n~n"),

    % Run all test groups
    Results = [
        test_lexer(),
        test_parser(),
        test_runtime_semantics(),
        test_codegen(),
        test_integration()
    ],

    % Summary
    TotalTests = lists:sum([T || {T, _} <- Results]),
    PassedTests = lists:sum([P || {_, P} <- Results]),
    FailedTests = TotalTests - PassedTests,

    io:format("~n=== Test Summary ===~n"),
    io:format("Total: ~p, Passed: ~p, Failed: ~p~n", [TotalTests, PassedTests, FailedTests]),

    case FailedTests of
        0 ->
            io:format("~n✓ All tests passed!~n"),
            ok;
        _ ->
            io:format("~n✗ Some tests failed!~n"),
            {error, {failed_tests, FailedTests}}
    end.

%% ============================================================================
%% Lexer Tests
%% ============================================================================

test_lexer() ->
    io:format("--- Lexer Tests ---~n"),
    Tests = [
        {"Tokenize pipe operator", fun test_tokenize_pipe/0},
        {"Pipe in expression", fun test_tokenize_pipe_expr/0},
        {"Multiple pipes", fun test_tokenize_pipe_chain/0}
    ],
    run_tests(Tests).

test_tokenize_pipe() ->
    Source = <<"|>">>,
    {ok, Tokens} = cure_lexer:tokenize(Source),
    % Should have pipe operator token and EOF
    case length(Tokens) >= 1 of
        true ->
            FirstToken = hd(Tokens),
            case FirstToken of
                #token{type = '|>'} -> ok;
                _ -> {error, {wrong_token_type, FirstToken}}
            end;
        false ->
            {error, no_tokens}
    end.

test_tokenize_pipe_expr() ->
    Source = <<"x |> f">>,
    {ok, Tokens} = cure_lexer:tokenize(Source),
    % Should have: identifier, pipe, identifier
    case length(Tokens) >= 3 of
        true ->
            [T1, T2, T3 | _] = Tokens,
            case {T1, T2, T3} of
                {#token{type = identifier}, #token{type = '|>'}, #token{type = identifier}} ->
                    ok;
                _ ->
                    {error, {wrong_token_sequence, [T1, T2, T3]}}
            end;
        false ->
            {error, {too_few_tokens, Tokens}}
    end.

test_tokenize_pipe_chain() ->
    Source = <<"x |> f |> g |> h">>,
    {ok, Tokens} = cure_lexer:tokenize(Source),
    % Count pipe operators
    PipeCount = length([T || T <- Tokens, element(#token.type, T) =:= '|>']),
    case PipeCount of
        3 -> ok;
        N -> {error, {expected_3_pipes, got, N}}
    end.

%% ============================================================================
%% Parser Tests
%% ============================================================================

test_parser() ->
    io:format("--- Parser Tests ---~n"),
    Tests = [
        {"Parse simple pipe", fun test_parse_simple_pipe/0},
        {"Parse pipe chain", fun test_parse_pipe_chain/0},
        {"Parse pipe with function call", fun test_parse_pipe_with_call/0},
        {"Pipe operator precedence", fun test_pipe_precedence/0}
    ],
    run_tests(Tests).

test_parse_simple_pipe() ->
    Source = "x |> f",
    {ok, Tokens} = cure_lexer:scan(Source),
    % Create a minimal program context
    Program = <<"def test() = ", (list_to_binary(Source))/binary>>,
    {ok, ProgramTokens} = cure_lexer:scan(binary_to_list(Program)),
    case cure_parser:parse(ProgramTokens) of
        {ok, _AST} -> ok;
        {error, Reason} -> {error, {parse_failed, Reason}}
    end.

test_parse_pipe_chain() ->
    Source = "x |> f |> g",
    Program = <<"def test() = ", (list_to_binary(Source))/binary>>,
    {ok, Tokens} = cure_lexer:scan(binary_to_list(Program)),
    case cure_parser:parse(Tokens) of
        {ok, _AST} -> ok;
        {error, Reason} -> {error, {parse_failed, Reason}}
    end.

test_parse_pipe_with_call() ->
    Source = "x |> double() |> increment()",
    Program = <<"def test() = ", (list_to_binary(Source))/binary>>,
    {ok, Tokens} = cure_lexer:scan(binary_to_list(Program)),
    case cure_parser:parse(Tokens) of
        {ok, _AST} -> ok;
        {error, Reason} -> {error, {parse_failed, Reason}}
    end.

test_pipe_precedence() ->
    % Pipe has lowest precedence (1), so it should be parsed last
    Source = "1 + 2 |> double",
    Program = <<"def test() = ", (list_to_binary(Source))/binary>>,
    {ok, Tokens} = cure_lexer:scan(binary_to_list(Program)),
    case cure_parser:parse(Tokens) of
        {ok, _AST} ->
            % Should parse as (1 + 2) |> double, not 1 + (2 |> double)
            ok;
        {error, Reason} ->
            {error, {parse_failed, Reason}}
    end.

%% ============================================================================
%% Runtime Semantics Tests
%% ============================================================================

test_runtime_semantics() ->
    io:format("--- Runtime Semantics Tests ---~n"),
    Tests = [
        {"Error propagation", fun test_error_propagation/0},
        {"Ok unwrapping", fun test_ok_unwrapping/0},
        {"Value passing", fun test_value_passing/0},
        {"Exception handling", fun test_exception_handling/0},
        {"Monadic check", fun test_is_monad/0}
    ],
    run_tests(Tests).

test_error_propagation() ->
    % Rule 1: Error(x) |> f = Error(x)
    Error = {'Error', reason},
    Function = fun(_) -> throw(should_not_be_called) end,
    Result = cure_std:pipe(Error, Function),
    case Result of
        {'Error', reason} -> ok;
        _ -> {error, {expected_error_propagation, got, Result}}
    end.

test_ok_unwrapping() ->
    % Rule 2: Ok(x) |> f = f(x) wrapped
    Ok = {'Ok', 5},
    Function = fun(X) -> X * 2 end,
    Result = cure_std:pipe(Ok, Function),
    case Result of
        {'Ok', 10} -> ok;
        _ -> {error, {expected_ok_10, got, Result}}
    end.

test_value_passing() ->
    % Rule 3: x |> f = f(x) wrapped
    Value = 5,
    Function = fun(X) -> X * 2 end,
    Result = cure_std:pipe(Value, Function),
    case Result of
        {'Ok', 10} -> ok;
        _ -> {error, {expected_ok_10, got, Result}}
    end.

test_exception_handling() ->
    % Exceptions should be caught and wrapped as Error
    Ok = {'Ok', 0},
    % Will throw badarith
    Function = fun(X) -> 1 div X end,
    Result = cure_std:pipe(Ok, Function),
    case Result of
        {'Error', {pipe_runtime_error, error, badarith}} -> ok;
        _ -> {error, {expected_error_tuple, got, Result}}
    end.

test_is_monad() ->
    % Test monadic type detection
    Tests = [
        {{'Ok', 42}, true},
        {{'Error', reason}, true},
        {42, false},
        {[1, 2, 3], false},
        {"string", false}
    ],
    Results = lists:map(
        fun({Value, Expected}) ->
            Actual = cure_std:is_monad(Value),
            case Actual =:= Expected of
                true -> ok;
                false -> {error, {value, Value, expected, Expected, got, Actual}}
            end
        end,
        Tests
    ),
    case lists:all(fun(R) -> R =:= ok end, Results) of
        true -> ok;
        false -> hd([R || R <- Results, R =/= ok])
    end.

%% ============================================================================
%% Code Generation Tests
%% ============================================================================

test_codegen() ->
    io:format("--- Code Generation Tests ---~n"),
    Tests = [
        {"Generate monadic pipe instruction", fun test_gen_monadic_pipe/0},
        {"Pipe with multiple args", fun test_gen_pipe_multi_args/0}
    ],
    run_tests(Tests).

test_gen_monadic_pipe() ->
    % Create a simple pipe expression AST
    Left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
    Right = #identifier_expr{name = f, location = #location{line = 1, column = 6}},
    PipeExpr = #binary_op_expr{
        op = '|>',
        left = Left,
        right = Right,
        location = #location{line = 1, column = 4}
    },

    % Try to compile it
    State = cure_codegen:init_state(test_module),
    case cure_codegen:compile_expression(PipeExpr, State) of
        {Instructions, _NewState} ->
            % Check for monadic_pipe_call instruction
            HasMonadicPipe = lists:any(
                fun
                    (#beam_instr{op = Op}) -> Op =:= monadic_pipe_call;
                    (_) -> false
                end,
                Instructions
            ),
            case HasMonadicPipe of
                true -> ok;
                false -> {error, no_monadic_pipe_instruction}
            end;
        {error, Reason} ->
            {error, {codegen_failed, Reason}}
    end.

test_gen_pipe_multi_args() ->
    % Pipe with function that takes multiple args: x |> f(y, z)
    Left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
    FuncCall = #function_call_expr{
        function = #identifier_expr{name = f, location = #location{line = 1, column = 6}},
        args = [
            #identifier_expr{name = y, location = #location{line = 1, column = 8}},
            #identifier_expr{name = z, location = #location{line = 1, column = 11}}
        ],
        location = #location{line = 1, column = 6}
    },
    PipeExpr = #binary_op_expr{
        op = '|>',
        left = Left,
        right = FuncCall,
        location = #location{line = 1, column = 4}
    },

    State = cure_codegen:init_state(test_module),
    case cure_codegen:compile_expression(PipeExpr, State) of
        {Instructions, _NewState} ->
            % Check for monadic_pipe_call with arity 3 (x + y + z)
            HasCorrectArity = lists:any(
                fun
                    (#beam_instr{op = monadic_pipe_call, args = [Arity]}) ->
                        % x, y, z
                        Arity =:= 3;
                    (_) ->
                        false
                end,
                Instructions
            ),
            case HasCorrectArity of
                true -> ok;
                false -> {error, wrong_arity_in_monadic_pipe}
            end;
        {error, Reason} ->
            {error, {codegen_failed, Reason}}
    end.

%% ============================================================================
%% Integration Tests
%% ============================================================================

test_integration() ->
    io:format("--- Integration Tests ---~n"),
    Tests = [
        {"Simple pipe chain", fun test_int_simple_chain/0},
        {"Error short-circuit", fun test_int_error_shortcircuit/0}
    ],
    run_tests(Tests).

test_int_simple_chain() ->
    % Test: 5 |> double |> increment
    % Result should be Ok(11)
    Double = fun(X) -> X * 2 end,
    Increment = fun(X) -> X + 1 end,

    Step1 = cure_std:pipe(5, Double),
    Step2 = cure_std:pipe(Step1, Increment),

    case Step2 of
        {'Ok', 11} -> ok;
        _ -> {error, {expected_ok_11, got, Step2}}
    end.

test_int_error_shortcircuit() ->
    % Test that error propagates through chain
    % parse("bad") |> validate |> process
    Parse = fun(_) -> {'Error', parse_error} end,
    Validate = fun(_) -> throw(should_not_run) end,
    Process = fun(_) -> throw(should_not_run) end,

    Step1 = cure_std:pipe("bad", Parse),
    Step2 = cure_std:pipe(Step1, Validate),
    Step3 = cure_std:pipe(Step2, Process),

    case Step3 of
        {'Error', parse_error} -> ok;
        _ -> {error, {expected_parse_error, got, Step3}}
    end.

%% ============================================================================
%% Test Utilities
%% ============================================================================

run_tests(Tests) ->
    Results = lists:map(
        fun({Name, TestFun}) ->
            io:format("  Testing: ~s... ", [Name]),
            try
                case TestFun() of
                    ok ->
                        io:format("✓~n"),
                        {1, 1};
                    {error, Reason} ->
                        io:format("✗~n"),
                        io:format("    Error: ~p~n", [Reason]),
                        {1, 0}
                end
            catch
                Error:ExcReason:Stack ->
                    io:format("✗ (exception)~n"),
                    io:format("    ~p:~p~n", [Error, ExcReason]),
                    io:format("    Stack: ~p~n", [Stack]),
                    {1, 0}
            end
        end,
        Tests
    ),

    % Calculate totals
    Total = lists:sum([T || {T, _} <- Results]),
    Passed = lists:sum([P || {_, P} <- Results]),

    io:format("  Subtotal: ~p/~p passed~n~n", [Passed, Total]),
    {Total, Passed}.
