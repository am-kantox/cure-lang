%% Enhanced Parser Tests
-module(enhanced_parser_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast_simple.hrl").

%% Run all tests
run() ->
    io:format("Running Enhanced Parser tests...~n"),
    test_list_literals(),
    test_function_calls(),
    test_multi_statement_functions(),
    io:format("All enhanced parser tests passed!~n").

%% Test list literal parsing
test_list_literals() ->
    Code = <<"def test() = [1, 2, 3]">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,
    ?assertMatch(#function_def{name = test}, FunctionDef),

    % Check that body is a list expression
    Body = FunctionDef#function_def.body,
    ?assertMatch(#list_expr{}, Body),

    % Check list elements
    #list_expr{elements = Elements} = Body,
    ?assertEqual(3, length(Elements)),

    io:format("✓ List literal parsing test passed~n").

%% Test function call parsing
test_function_calls() ->
    Code = <<"def test() = Math.add(1, 2)">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,

    % Check that body is a function call
    Body = FunctionDef#function_def.body,
    ?assertMatch(#function_call_expr{}, Body),

    % Check function call structure
    #function_call_expr{function = Function, args = Args} = Body,
    ?assertEqual(2, length(Args)),
    ?assertMatch(#binary_op_expr{op = '.'}, Function),

    io:format("✓ Function call parsing test passed~n").

%% Test multi-statement function bodies
test_multi_statement_functions() ->
    Code =
        <<
            "def test() = \n"
            "              let x = 5\n"
            "              let y = 10\n"
            "              x + y"
        >>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,

    % Check that body is a block expression
    Body = FunctionDef#function_def.body,
    ?assertMatch(#block_expr{}, Body),

    % Check block structure
    #block_expr{expressions = Expressions} = Body,
    % let x, let y, x + y
    ?assertEqual(3, length(Expressions)),

    % First expression should be let
    [FirstExpr | _] = Expressions,
    ?assertMatch(#let_expr{}, FirstExpr),

    io:format("✓ Multi-statement function parsing test passed~n").
