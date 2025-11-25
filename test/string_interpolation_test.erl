-module(string_interpolation_test).

-export([
    run/0,
    test_basic_interpolation/0,
    test_expression_interpolation/0,
    test_nested_interpolation/0,
    test_escape_sequences/0,
    test_multiline_interpolation/0
]).

-include("../src/parser/cure_ast.hrl").

%% @doc Main test runner
run() ->
    io:format("~n=== String Interpolation Tests ===~n~n"),

    Tests = [
        {"Basic variable interpolation", fun test_basic_interpolation/0},
        {"Expression interpolation", fun test_expression_interpolation/0},
        {"Nested interpolation", fun test_nested_interpolation/0},
        {"Escape sequences in interpolation", fun test_escape_sequences/0},
        {"Multiline string interpolation", fun test_multiline_interpolation/0}
    ],

    Results = lists:map(
        fun({Name, TestFun}) ->
            io:format("Running: ~s~n", [Name]),
            try
                TestFun(),
                io:format("  ✓ PASS~n"),
                pass
            catch
                Class:Error:Stack ->
                    io:format("  ✗ FAIL: ~p:~p~n", [Class, Error]),
                    io:format("  Stack: ~p~n", [Stack]),
                    fail
            end
        end,
        Tests
    ),

    % Check if all passed
    AllPassed = lists:all(fun(Result) -> Result =:= pass end, Results),

    io:format("~n"),
    case AllPassed of
        true ->
            io:format("All string interpolation tests passed!~n"),
            ok;
        false ->
            io:format("Some tests failed!~n"),
            error
    end.

%% @doc Test basic variable interpolation
test_basic_interpolation() ->
    % Test simple variable interpolation
    Source1 = <<
        "module InterpolTest do\n"
        "  def greet(name: String): String =\n"
        "    \"Hello, #{name}!\"\n"
        "  \n"
        "  def show_age(age: Int): String =\n"
        "    \"You are #{age} years old\"\n"
        "end\n"
    >>,

    {ok, Tokens1} = cure_lexer:tokenize(Source1),
    {ok, AST1} = cure_parser:parse(Tokens1),

    % Verify parsing succeeded
    true = is_list(AST1),
    true = length(AST1) > 0,

    % Test multiple interpolations in one string
    Source2 = <<
        "module MultiInterpol do\n"
        "  def full_name(first: String, last: String): String =\n"
        "    \"Name: #{first} #{last}\"\n"
        "  \n"
        "  def coords(x: Int, y: Int): String =\n"
        "    \"Point(#{x}, #{y})\"\n"
        "end\n"
    >>,

    {ok, Tokens2} = cure_lexer:tokenize(Source2),
    {ok, _AST2} = cure_parser:parse(Tokens2),

    ok.

%% @doc Test expression interpolation
test_expression_interpolation() ->
    % Test arithmetic expressions in interpolation
    Source1 = <<
        "module ExprInterpol do\n"
        "  def calculate(a: Int, b: Int): String =\n"
        "    \"Sum: #{a + b}\"\n"
        "  \n"
        "  def multiply(x: Int, y: Int): String =\n"
        "    \"Result: #{x * y}\"\n"
        "end\n"
    >>,

    {ok, Tokens1} = cure_lexer:tokenize(Source1),
    {ok, AST1} = cure_parser:parse(Tokens1),

    % Verify parsing succeeded
    true = is_list(AST1),
    true = length(AST1) > 0,

    ok.

%% @doc Test nested/complex interpolation scenarios
test_nested_interpolation() ->
    % Test interpolation within if expressions
    Source1 = <<
        "module IfInterpol do\n"
        "  def describe(n: Int): String =\n"
        "    if n > 0 then \"Positive: #{n}\" else \"Non-positive\"\n"
        "end\n"
    >>,

    {ok, Tokens1} = cure_lexer:tokenize(Source1),
    {ok, AST1} = cure_parser:parse(Tokens1),

    % Verify parsing succeeded
    true = is_list(AST1),
    true = length(AST1) > 0,

    ok.

%% @doc Test escape sequences with interpolation
test_escape_sequences() ->
    % Test that interpolation works with escape sequences
    Source1 = <<
        "module EscapeInterpol do\n"
        "  def quoted(name: String): String =\n"
        "    \"\\\"#{name}\\\"\"\n"
        "  \n"
        "  def newline(msg: String): String =\n"
        "    \"Message:\\n#{msg}\"\n"
        "  \n"
        "  def tabs(a: Int, b: Int): String =\n"
        "    \"#{a}\\t#{b}\"\n"
        "end\n"
    >>,

    {ok, Tokens1} = cure_lexer:tokenize(Source1),
    {ok, AST1} = cure_parser:parse(Tokens1),

    % Verify parsing succeeded
    true = is_list(AST1),
    true = length(AST1) > 0,

    % Test escaped braces (literal #{})
    Source2 = <<
        "module LiteralBraces do\n"
        "  def show(): String =\n"
        "    \"Use \\#{expr} for interpolation\"\n"
        "end\n"
    >>,

    {ok, Tokens2} = cure_lexer:tokenize(Source2),
    {ok, _AST2} = cure_parser:parse(Tokens2),

    ok.

%% @doc Test multiline strings with interpolation
test_multiline_interpolation() ->
    % Test interpolation in multiline strings
    Source = <<
        "module MultilineInterpol do\n"
        "  def report(name: String, age: Int, city: String): String =\n"
        "    \"\"\"Person Report:\n"
        "    Name: #{name}\n"
        "    Age: #{age}\n"
        "    City: #{city}\"\"\"\n"
        "  \n"
        "  def table_row(id: Int, value: String): String =\n"
        "    \"\"\"| #{id} | #{value} |\"\"\"\n"
        "end\n"
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Source),
    {ok, AST} = cure_parser:parse(Tokens),

    % Verify parsing succeeded
    true = is_list(AST),
    true = length(AST) > 0,

    ok.
