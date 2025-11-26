%% Simple standalone test for Melquíades operator (|->)
-module(melquiades_simple_test).

-export([run/0]).

-include("../src/parser/cure_ast.hrl").

%% Run all tests
run() ->
    io:format("Running Melquíades operator tests...~n"),
    test_lexer(),
    test_parser(),
    test_codegen(),
    io:format("All Melquíades tests passed!~n"),
    ok.

%% Test that the lexer recognizes |-> token
test_lexer() ->
    Code = <<"msg |-> :server">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),

    % Extract token types
    Types = [element(2, T) || T <- Tokens],

    % Verify melquiades_send token is present
    case lists:member(melquiades_send, Types) of
        true ->
            io:format("  ✓ Lexer test passed~n"),
            ok;
        false ->
            io:format("  ✗ Lexer test FAILED: melquiades_send token not found~n"),
            io:format("  Token types: ~p~n", [Types]),
            error(lexer_test_failed)
    end.

%% Test that the parser creates correct AST
test_parser() ->
    Code = <<"def test() -> None do\n  msg |-> :server\nend">>,

    case cure_lexer:tokenize(Code) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, _AST} ->
                    io:format("  ✓ Parser test passed~n"),
                    ok;
                {error, Reason} ->
                    io:format("  ✗ Parser test FAILED: ~p~n", [Reason]),
                    error(parser_test_failed)
            end;
        {error, LexReason} ->
            io:format("  ✗ Lexer failed in parser test: ~p~n", [LexReason]),
            error(lexer_failed_in_parser_test)
    end.

%% Test that codegen produces correct instructions
test_codegen() ->
    % Create a simple Melquiades send expression
    MelquiadesExpr = #melquiades_send_expr{
        message = #identifier_expr{name = msg, location = undefined},
        target = #identifier_expr{name = server, location = undefined},
        location = undefined
    },

    % Try to compile it
    try
        {Instructions, _State} = cure_codegen:compile_expression(MelquiadesExpr),

        % Check that we got some instructions
        case length(Instructions) > 0 of
            true ->
                io:format("  ✓ Codegen test passed (~p instructions)~n", [length(Instructions)]),
                ok;
            false ->
                io:format("  ✗ Codegen test FAILED: no instructions generated~n"),
                error(codegen_test_failed)
        end
    catch
        Type:Error ->
            io:format("  ✗ Codegen test FAILED: ~p:~p~n", [Type, Error]),
            error(codegen_test_failed)
    end.
