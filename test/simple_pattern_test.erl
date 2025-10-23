%% Simple Pattern Matching Test
%% Basic test to verify pattern matching features

-module(simple_pattern_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast.hrl").

%% Test runner
run() ->
    cure_utils:debug("~n=== Simple Pattern Matching Test ===~n"),

    try
        test_case_expression_basic(),
        cure_utils:debug("✓ Case expression basic test passed~n"),

        test_record_pattern_basic(),
        cure_utils:debug("✓ Record pattern basic test passed~n"),

        test_constructor_pattern_basic(),
        cure_utils:debug("✓ Constructor pattern basic test passed~n"),

        cure_utils:debug("All simple pattern matching tests passed!~n")
    catch
        Error:Reason:Stacktrace ->
            cure_utils:debug("Test failed: ~p:~p~n", [Error, Reason]),
            cure_utils:debug("Stacktrace: ~p~n", [Stacktrace])
    end.

%% Test basic case expression parsing
test_case_expression_basic() ->
    Code = <<"def test(x) = case x of 1 -> \"one\" _ -> \"other\" end">>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,
    ?assertMatch(#function_def{name = test}, FunctionDef),

    Body = FunctionDef#function_def.body,
    ?assertMatch(#match_expr{}, Body),

    ok.

%% Test basic record pattern parsing
test_record_pattern_basic() ->
    Code =
        <<"record Person do name: String age: Int end def greet(p: Person): String = match p do Person{name: n} -> n end">>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(2, length(AST)),
    [RecordDef, FunctionDef] = AST,

    ?assertMatch(#record_def{name = 'Person'}, RecordDef),
    ?assertMatch(#function_def{name = greet}, FunctionDef),

    ok.

%% Test basic constructor pattern parsing
test_constructor_pattern_basic() ->
    Code = <<"def test(opt) = case opt of Some(x) -> x None -> 0 end">>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,
    ?assertMatch(#function_def{name = test}, FunctionDef),

    Body = FunctionDef#function_def.body,
    ?assertMatch(#match_expr{}, Body),

    ok.
