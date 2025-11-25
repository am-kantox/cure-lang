-module(negative_number_test).

-export([
    run/0,
    test_negative_literals/0,
    test_negative_arithmetic/0,
    test_negative_comparisons/0,
    test_negative_edge_cases/0
]).

-include("../src/parser/cure_ast.hrl").

%% @doc Main test runner
run() ->
    io:format("~n=== Negative Number Handling Tests ===~n~n"),

    Tests = [
        {"Negative literals", fun test_negative_literals/0},
        {"Negative number arithmetic", fun test_negative_arithmetic/0},
        {"Negative comparisons", fun test_negative_comparisons/0},
        {"Edge cases", fun test_negative_edge_cases/0}
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
            io:format("All negative number tests passed!~n"),
            ok;
        false ->
            io:format("Some tests failed!~n"),
            error
    end.

%% @doc Test negative number literals
test_negative_literals() ->
    % Test basic negative integers
    Source1 = <<
        "module NegLiterals do\n"
        "  def neg_one(): Int = -1\n"
        "  def neg_hundred(): Int = -100\n"
        "  def neg_million(): Int = -1000000\n"
        "  def zero(): Int = 0\n"
        "  def positive(): Int = 42\n"
        "end\n"
    >>,

    {ok, Tokens1} = cure_lexer:tokenize(Source1),
    {ok, AST1} = cure_parser:parse(Tokens1),

    % Verify parsing succeeded
    true = is_list(AST1),
    true = length(AST1) > 0,

    % Test negative floats
    Source2 = <<
        "module NegFloats do\n"
        "  def neg_point_five(): Float = -0.5\n"
        "  def neg_pi(): Float = -3.14159\n"
        "  def neg_large(): Float = -999.999\n"
        "end\n"
    >>,

    {ok, Tokens2} = cure_lexer:tokenize(Source2),
    {ok, _AST2} = cure_parser:parse(Tokens2),

    ok.

%% @doc Test arithmetic with negative numbers
test_negative_arithmetic() ->
    % Test addition with negatives
    Source1 = <<
        "module NegAddition do\n"
        "  def add_neg(a: Int): Int = a + (-5)\n"
        "  def neg_add_pos(a: Int): Int = -10 + a\n"
        "  def neg_add_neg(): Int = -5 + (-3)\n"
        "end\n"
    >>,

    {ok, Tokens1} = cure_lexer:tokenize(Source1),
    {ok, AST1} = cure_parser:parse(Tokens1),

    % Verify parsing succeeded
    true = is_list(AST1),
    true = length(AST1) > 0,

    % Test subtraction with negatives
    Source2 = <<
        "module NegSubtraction do\n"
        "  def sub_neg(a: Int): Int = a - (-5)\n"
        "  def neg_sub_pos(): Int = -10 - 5\n"
        "  def neg_sub_neg(): Int = -5 - (-3)\n"
        "end\n"
    >>,

    {ok, Tokens2} = cure_lexer:tokenize(Source2),
    {ok, _AST2} = cure_parser:parse(Tokens2),

    % Test multiplication with negatives
    Source3 = <<
        "module NegMultiply do\n"
        "  def mul_neg(a: Int): Int = a * (-2)\n"
        "  def neg_mul_pos(): Int = -5 * 3\n"
        "  def neg_mul_neg(): Int = -4 * (-3)\n"
        "end\n"
    >>,

    {ok, Tokens3} = cure_lexer:tokenize(Source3),
    {ok, _AST3} = cure_parser:parse(Tokens3),

    % Test division with negatives
    Source4 = <<
        "module NegDivision do\n"
        "  def div_neg(a: Int): Int = a / (-2)\n"
        "  def neg_div_pos(): Int = -10 / 2\n"
        "  def neg_div_neg(): Int = -12 / (-3)\n"
        "end\n"
    >>,

    {ok, Tokens4} = cure_lexer:tokenize(Source4),
    {ok, _AST4} = cure_parser:parse(Tokens4),

    ok.

%% @doc Test comparisons with negative numbers
test_negative_comparisons() ->
    Source = <<
        "module NegComparisons do\n"
        "  def less_than_neg(a: Int): Bool = a < -5\n"
        "  def greater_than_neg(a: Int): Bool = a > -10\n"
        "  def equals_neg(a: Int): Bool = a == -7\n"
        "  def lte_neg(a: Int): Bool = a <= -1\n"
        "  def gte_neg(a: Int): Bool = a >= -100\n"
        "  def not_equals_neg(a: Int): Bool = a != -42\n"
        "  \n"
        "  def neg_less_neg(): Bool = -10 < -5\n"
        "  def neg_greater_neg(): Bool = -5 > -10\n"
        "end\n"
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Source),
    {ok, AST} = cure_parser:parse(Tokens),

    % Verify parsing succeeded
    true = is_list(AST),
    true = length(AST) > 0,

    ok.

%% @doc Test edge cases with negative numbers
test_negative_edge_cases() ->
    % Test negative in function parameters
    Source1 = <<
        "module NegParams do\n"
        "  def use_neg(): Int = abs(-42)\n"
        "  def multi_neg(): Int = max(-5, -10)\n"
        "end\n"
    >>,

    {ok, Tokens1} = cure_lexer:tokenize(Source1),
    {ok, AST1} = cure_parser:parse(Tokens1),

    % Verify parsing succeeded
    true = is_list(AST1),
    true = length(AST1) > 0,

    % Test negative in parenthesized expressions
    Source3 = <<
        "module NegParens do\n"
        "  def paren_neg(): Int = (-5) + (-3)\n"
        "  def nested_paren(): Int = ((-10) * (-2))\n"
        "end\n"
    >>,

    {ok, Tokens3} = cure_lexer:tokenize(Source3),
    {ok, _AST3} = cure_parser:parse(Tokens3),

    % Test unary minus on expressions
    Source4 = <<
        "module UnaryMinus do\n"
        "  def negate_var(x: Int): Int = -x\n"
        "  def negate_expr(a: Int, b: Int): Int = -(a + b)\n"
        "  def double_neg(x: Int): Int = -(-x)\n"
        "end\n"
    >>,

    {ok, Tokens4} = cure_lexer:tokenize(Source4),
    {ok, _AST4} = cure_parser:parse(Tokens4),

    ok.
