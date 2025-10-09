%% Cure Programming Language - Lexer Tests
-module(lexer_test).

-export([run/0, test_basic_tokens/0, test_keywords/0, test_operators/0, test_literals/0]).

%% Include lexer for testing
-include_lib("eunit/include/eunit.hrl").

%% Token record definition (should match lexer)
-record(token, {
    type :: atom(),
    value :: term(),
    line :: integer(),
    column :: integer()
}).

%% Run all tests
run() ->
    io:format("Running Cure lexer tests...~n"),
    test_basic_tokens(),
    test_keywords(),
    test_operators(),
    test_literals(),
    io:format("All lexer tests passed!~n").

%% Test basic token recognition
test_basic_tokens() ->
    Code = <<"def hello() = \"world\"">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),

    Expected = [
        {def, def, 1, 1},
        {identifier, <<"hello">>, 1, 5},
        {'(', '(', 1, 10},
        {')', ')', 1, 11},
        {'=', '=', 1, 13},
        {string, "world", 1, 15}
    ],

    ActualSimple = [
        {T#token.type, T#token.value, T#token.line, T#token.column}
     || T <- Tokens
    ],

    ?assertEqual(Expected, ActualSimple),
    io:format("✓ Basic tokens test passed~n").

%% Test keyword recognition
test_keywords() ->
    Code = <<"module def end do if then else match when">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),

    KeywordTypes = [cure_lexer:token_type(T) || T <- Tokens],
    Expected = [module, def, 'end', do, 'if', then, 'else', match, 'when'],

    ?assertEqual(Expected, KeywordTypes),
    io:format("✓ Keywords test passed~n").

%% Test operator recognition
test_operators() ->
    Code = <<"-> = + - * / < > <= >= == != :: ++">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),

    OpTypes = [cure_lexer:token_type(T) || T <- Tokens],
    Expected = ['->', '=', '+', '-', '*', '/', '<', '>', '<=', '>=', '==', '!=', '::', '++'],

    ?assertEqual(Expected, OpTypes),
    io:format("✓ Operators test passed~n").

%% Test literal recognition
test_literals() ->
    % Test numbers
    {ok, Tokens1} = cure_lexer:tokenize(<<"42 3.14">>),
    ?assertEqual([42, 3.14], [T#token.value || T <- Tokens1]),

    % Test strings
    {ok, Tokens2} = cure_lexer:tokenize(<<"\"hello world\"">>),
    ?assertEqual(["hello world"], [T#token.value || T <- Tokens2]),

    % Test atoms
    {ok, Tokens3} = cure_lexer:tokenize(<<":atom :another_atom">>),
    ?assertEqual([atom, another_atom], [T#token.value || T <- Tokens3]),

    % Test identifiers
    {ok, Tokens4} = cure_lexer:tokenize(<<"variable_name function_name?">>),
    ?assertEqual([<<"variable_name">>, <<"function_name?">>], [T#token.value || T <- Tokens4]),

    io:format("✓ Literals test passed~n").
