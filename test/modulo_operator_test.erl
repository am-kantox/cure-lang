-module(modulo_operator_test).

-export([
    run/0,
    test_basic_modulo/0,
    test_negative_modulo/0,
    test_large_numbers/0,
    test_zero_cases/0,
    test_modulo_properties/0
]).

-include("../src/parser/cure_ast.hrl").

%% @doc Main test runner
run() ->
    io:format("~n=== Modulo Operator (%) Tests ===~n~n"),

    Tests = [
        {"Basic modulo operations", fun test_basic_modulo/0},
        {"Negative number modulo", fun test_negative_modulo/0},
        {"Large number modulo", fun test_large_numbers/0},
        {"Zero edge cases", fun test_zero_cases/0},
        {"Modulo properties", fun test_modulo_properties/0}
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
            io:format("All modulo operator tests passed!~n"),
            ok;
        false ->
            io:format("Some tests failed!~n"),
            error
    end.

%% @doc Test basic modulo operations
test_basic_modulo() ->
    % Test basic positive number modulo
    Source1 = <<
        "module ModuloTest do\n"
        "  def test1(): Int = 10 % 3\n"
        "  def test2(): Int = 15 % 4\n"
        "  def test3(): Int = 7 % 7\n"
        "  def test4(): Int = 5 % 10\n"
        "end\n"
    >>,

    {ok, Tokens1} = cure_lexer:tokenize(Source1),
    {ok, AST1} = cure_parser:parse(Tokens1),

    % Verify parsing succeeded and we have definitions
    true = is_list(AST1),
    true = length(AST1) > 0,

    % Test basic modulo compilation
    Source2 = <<
        "module FizzBuzzMod do\n"
        "  def fizzbuzz(n: Int): String =\n"
        "    match {n % 3, n % 5} do\n"
        "      {0, 0} -> \"FizzBuzz\"\n"
        "      {0, _} -> \"Fizz\"\n"
        "      {_, 0} -> \"Buzz\"\n"
        "      _ -> \"Number\"\n"
        "    end\n"
        "end\n"
    >>,

    {ok, Tokens2} = cure_lexer:tokenize(Source2),
    {ok, _AST2} = cure_parser:parse(Tokens2),

    ok.

%% @doc Test modulo with negative numbers
test_negative_modulo() ->
    % Erlang rem behavior: sign of result matches sign of dividend
    % -10 rem 3 = -1 (not 2)
    % 10 rem -3 = 1 (not -2)

    Source = <<
        "module NegModTest do\n"
        "  def neg_dividend(): Int = -10 % 3\n"
        "  def neg_divisor(): Int = 10 % -3\n"
        "  def both_neg(): Int = -10 % -3\n"
        "  def large_neg(): Int = -100 % 7\n"
        "end\n"
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Source),
    {ok, AST} = cure_parser:parse(Tokens),

    % Verify parsing succeeded
    true = is_list(AST),
    true = length(AST) > 0,

    ok.

%% @doc Test modulo with large numbers
test_large_numbers() ->
    Source = <<
        "module LargeModTest do\n"
        "  def large1(): Int = 1000000 % 7\n"
        "  def large2(): Int = 999999999 % 12345\n"
        "  def large3(): Int = 2147483647 % 1000\n"
        "end\n"
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Source),
    {ok, AST} = cure_parser:parse(Tokens),

    % Verify parsing succeeded
    true = is_list(AST),
    true = length(AST) > 0,
    ok.

%% @doc Test edge cases with zero
test_zero_cases() ->
    % Test 0 % n (always 0)
    Source1 = <<
        "module ZeroModTest do\n"
        "  def zero_dividend(): Int = 0 % 5\n"
        "  def zero_dividend2(): Int = 0 % 999\n"
        "end\n"
    >>,

    {ok, Tokens1} = cure_lexer:tokenize(Source1),
    {ok, _AST1} = cure_parser:parse(Tokens1),

    % Note: n % 0 should be caught at runtime (division by zero)
    % We test that it at least parses
    Source2 = <<
        "module ZeroDivisorMod do\n"
        "  def zero_divisor(): Int = 10 % 0\n"
        "end\n"
    >>,

    {ok, Tokens2} = cure_lexer:tokenize(Source2),
    {ok, _AST2} = cure_parser:parse(Tokens2),
    % Parser should accept it, runtime will error

    ok.

%% @doc Test mathematical properties of modulo
test_modulo_properties() ->
    % Test that modulo appears in expressions correctly
    Source = <<
        "module ModPropsTest do\n"
        "  def sum_of_mods(a: Int, b: Int, m: Int): Int =\n"
        "    (a % m) + (b % m)\n"
        "  \n"
        "  def product_mod(a: Int, b: Int, m: Int): Int =\n"
        "    (a * b) % m\n"
        "  \n"
        "  def chain_mod(n: Int): Int =\n"
        "    (n % 10) % 3\n"
        "  \n"
        "  def mod_in_condition(n: Int): Bool =\n"
        "    (n % 2) == 0\n"
        "end\n"
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Source),
    {ok, AST} = cure_parser:parse(Tokens),

    % Verify parsing succeeded - all modulo expressions should parse
    true = is_list(AST),
    true = length(AST) > 0,

    ok.
