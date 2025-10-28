-module(monomorphization_simple_test).

-export([run/0]).

-include("../src/parser/cure_ast.hrl").

run() ->
    io:format("Running Simple Monomorphization Tests...~n"),

    Tests = [
        fun test_identity_function/0,
        fun test_list_map/0,
        fun test_option_type/0
    ],

    Results = lists:map(
        fun(Test) ->
            try
                Test(),
                {ok, Test}
            catch
                Error:Reason:Stack ->
                    io:format("Test ~p failed: ~p:~p~n", [Test, Error, Reason]),
                    {error, Test, {Error, Reason}}
            end
        end,
        Tests
    ),

    Passed = length([ok || {ok, _} <- Results]),
    Failed = length([error || {error, _, _} <- Results]),

    io:format("~nMonomorphization Tests: ~p passed, ~p failed~n", [Passed, Failed]),

    case Failed of
        0 -> ok;
        _ -> erlang:halt(1)
    end.

test_identity_function() ->
    io:format("  Testing identity function...~n"),
    Source = <<"def id<T>(x: T): T do x end">>,

    case cure_lexer:tokenize(Source) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, _AST} -> ok;
                {error, Error} -> throw({parse_error, Error})
            end;
        {error, Error} ->
            throw({lex_error, Error})
    end.

test_list_map() ->
    io:format("  Testing list map function...~n"),
    Source =
        <<"def map<T, U>(f: T -> U, xs: List(T)): List(U) do\n    match xs do\n        [] -> []\n        [h | t] -> [f(h) | map(f, t)]\n    end\nend">>,

    case cure_lexer:tokenize(Source) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, _AST} -> ok;
                {error, Error} -> throw({parse_error, Error})
            end;
        {error, Error} ->
            throw({lex_error, Error})
    end.

test_option_type() ->
    io:format("  Testing Option type...~n"),
    Source =
        <<"def unwrap<T>(opt: Option(T), default: T): T do\n    match opt do\n        Some(x) -> x\n        None -> default\n    end\nend">>,

    case cure_lexer:tokenize(Source) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, _AST} -> ok;
                {error, Error} -> throw({parse_error, Error})
            end;
        {error, Error} ->
            throw({lex_error, Error})
    end.
