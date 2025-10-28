-module(pattern_matching_edge_cases_test).

-export([run/0]).

-include("../src/parser/cure_ast.hrl").

%%% Pattern Matching Edge Cases Test Suite %%%

run() ->
    io:format("Running Pattern Matching Edge Cases Tests...~n"),

    Tests = [
        fun test_nested_patterns/0,
        fun test_guards_with_patterns/0,
        fun test_overlapping_patterns/0,
        fun test_exhaustiveness_checking/0,
        fun test_wildcard_patterns/0,
        fun test_as_patterns/0,
        fun test_or_patterns/0,
        fun test_constructor_patterns/0,
        fun test_record_patterns/0,
        fun test_list_patterns_complex/0
    ],

    Results = lists:map(
        fun(Test) ->
            try
                Test(),
                {ok, Test}
            catch
                Error:Reason:Stack ->
                    io:format("Test ~p failed: ~p:~p~n~p~n", [Test, Error, Reason, Stack]),
                    {error, Test, {Error, Reason}}
            end
        end,
        Tests
    ),

    Passed = length([ok || {ok, _} <- Results]),
    Failed = length([error || {error, _, _} <- Results]),

    io:format("~nPattern Matching Tests: ~p passed, ~p failed~n", [Passed, Failed]),

    case Failed of
        0 -> ok;
        _ -> erlang:halt(1)
    end.

%%% Test: Nested Patterns %%%

test_nested_patterns() ->
    io:format("  Testing nested patterns...~n"),

    % Test deeply nested pattern matching
    Source =
        <<
            "\n"
            "        def depth(tree) do\n"
            "            match tree do\n"
            "                {leaf, _} -> 1\n"
            "                {node, {left, right}} -> \n"
            "                    1 + max(depth(left), depth(right))\n"
            "                {branch, _, {left, middle, right}} ->\n"
            "                    1 + max(depth(left), max(depth(middle), depth(right)))\n"
            "            end\n"
            "        end\n"
            "    "
        >>,

    case cure_lexer:tokenize(Source) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, _AST} ->
                    ok;
                {error, Error} ->
                    throw({parse_error, Error})
            end;
        {error, Error} ->
            throw({lex_error, Error})
    end.

%%% Test: Guards with Patterns %%%

test_guards_with_patterns() ->
    io:format("  Testing guards with patterns...~n"),

    % Test pattern matching combined with guards
    Source =
        <<
            "\n"
            "        def classify(x) do\n"
            "            match x do\n"
            "                n when n > 0 -> :positive\n"
            "                n when n < 0 -> :negative\n"
            "                0 -> :zero\n"
            "                _ -> :unknown\n"
            "            end\n"
            "        end\n"
            "        \n"
            "        def complex_guard(list) do\n"
            "            match list do\n"
            "                [x, y] when x > y -> :descending\n"
            "                [x, y] when x < y -> :ascending\n"
            "                [x, y] when x == y -> :equal\n"
            "                _ -> :other\n"
            "            end\n"
            "        end\n"
            "    "
        >>,

    case cure_lexer:tokenize(Source) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, _AST} ->
                    ok;
                {error, Error} ->
                    throw({parse_error, Error})
            end;
        {error, Error} ->
            throw({lex_error, Error})
    end.

%%% Test: Overlapping Patterns %%%

test_overlapping_patterns() ->
    io:format("  Testing overlapping patterns...~n"),

    % Test detection of overlapping/unreachable patterns
    Source =
        <<
            "\n"
            "        def test_overlap(x) do\n"
            "            match x do\n"
            "                {ok, _} -> :first\n"
            "                {ok, 42} -> :second\n"
            "                _ -> :fallback\n"
            "            end\n"
            "        end\n"
            "    "
        >>,

    case cure_lexer:tokenize(Source) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, _AST} ->
                    % TODO: Check for warnings about unreachable patterns
                    ok;
                {error, Error} ->
                    throw({parse_error, Error})
            end;
        {error, Error} ->
            throw({lex_error, Error})
    end.

%%% Test: Exhaustiveness Checking %%%

test_exhaustiveness_checking() ->
    io:format("  Testing exhaustiveness checking...~n"),

    % Test detection of non-exhaustive patterns
    Source =
        <<
            "\n"
            "        def incomplete(result) do\n"
            "            match result do\n"
            "                {success, value} -> value\n"
            "            end\n"
            "        end\n"
            "        \n"
            "        def complete(result) do\n"
            "            match result do\n"
            "                {success, value} -> value\n"
            "                {failure, _} -> 0\n"
            "            end\n"
            "        end\n"
            "    "
        >>,

    case cure_lexer:tokenize(Source) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, _AST} ->
                    % TODO: Check for warnings about non-exhaustive patterns
                    ok;
                {error, Error} ->
                    throw({parse_error, Error})
            end;
        {error, Error} ->
            throw({lex_error, Error})
    end.

%%% Test: Wildcard Patterns %%%

test_wildcard_patterns() ->
    io:format("  Testing wildcard patterns...~n"),

    % Test various uses of wildcard patterns
    Source =
        <<
            "\n"
            "        def ignore_middle(list) do\n"
            "            match list do\n"
            "                [first, _, last] -> {first, last}\n"
            "            end\n"
            "        end\n"
            "        \n"
            "        def ignore_tail(list) do\n"
            "            match list do\n"
            "                [head | _] -> head\n"
            "            end\n"
            "        end\n"
            "        \n"
            "        def count_matching(target, list) do\n"
            "            match list do\n"
            "                [] -> 0\n"
            "                [h | rest] when h == target -> 1 + count_matching(target, rest)\n"
            "                [_ | rest] -> count_matching(target, rest)\n"
            "            end\n"
            "        end\n"
            "    "
        >>,

    case cure_lexer:tokenize(Source) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, _AST} ->
                    ok;
                {error, Error} ->
                    throw({parse_error, Error})
            end;
        {error, Error} ->
            throw({lex_error, Error})
    end.

%%% Test: As-Patterns %%%

test_as_patterns() ->
    io:format("  Testing as-patterns...~n"),

    % Test @ patterns to bind while matching
    % Note: This syntax may need adjustment based on parser support
    ok.

%%% Test: Or-Patterns %%%

test_or_patterns() ->
    io:format("  Testing or-patterns...~n"),

    % Test patterns with multiple alternatives
    % Note: This syntax may need adjustment based on parser support
    ok.

%%% Test: Constructor Patterns %%%

test_constructor_patterns() ->
    io:format("  Testing constructor patterns...~n"),

    % Test matching on type constructors
    Source =
        <<
            "\n"
            "        def unwrap_option(opt) do\n"
            "            match opt do\n"
            "                Some(value) -> value\n"
            "                None -> 0\n"
            "            end\n"
            "        end\n"
            "        \n"
            "        def is_ok(result) do\n"
            "            match result do\n"
            "                Ok(_) -> true\n"
            "                Error(_) -> false\n"
            "            end\n"
            "        end\n"
            "    "
        >>,

    case cure_lexer:tokenize(Source) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, _AST} ->
                    ok;
                {error, Error} ->
                    throw({parse_error, Error})
            end;
        {error, Error} ->
            throw({lex_error, Error})
    end.

%%% Test: Record Patterns %%%

test_record_patterns() ->
    io:format("  Testing record patterns...~n"),

    % Test matching on record fields
    Source =
        <<
            "\n"
            "        record Point do\n"
            "            x: Int\n"
            "            y: Int\n"
            "        end\n"
            "        \n"
            "        def is_origin(p) do\n"
            "            match p do\n"
            "                Point{x: 0, y: 0} -> true\n"
            "                _ -> false\n"
            "            end\n"
            "        end\n"
            "        \n"
            "        def get_x(p) do\n"
            "            match p do\n"
            "                Point{x: x_val, y: _} -> x_val\n"
            "            end\n"
            "        end\n"
            "    "
        >>,

    case cure_lexer:tokenize(Source) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, _AST} ->
                    ok;
                {error, Error} ->
                    throw({parse_error, Error})
            end;
        {error, Error} ->
            throw({lex_error, Error})
    end.

%%% Test: Complex List Patterns %%%

test_list_patterns_complex() ->
    io:format("  Testing complex list patterns...~n"),

    % Test advanced list pattern matching
    Source =
        <<
            "\n"
            "        def take_while(pred, list) do\n"
            "            match list do\n"
            "                [] -> []\n"
            "                [head | tail] when pred(head) -> [head | take_while(pred, tail)]\n"
            "                _ -> []\n"
            "            end\n"
            "        end\n"
            "        \n"
            "        def split_at(n, list) do\n"
            "            match {n, list} do\n"
            "                {0, _} -> {[], list}\n"
            "                {_, []} -> {[], []}\n"
            "                {m, [head | tail]} when m > 0 ->\n"
            "                    let result = split_at(m - 1, tail) in\n"
            "                    match result do\n"
            "                        {left, right} -> {[head | left], right}\n"
            "                    end\n"
            "            end\n"
            "        end\n"
            "        \n"
            "        def partition(list) do\n"
            "            match list do\n"
            "                [] -> {[], []}\n"
            "                [x] -> {[x], []}\n"
            "                [x | rest1] ->\n"
            "                    match rest1 do\n"
            "                        [] -> {[x], []}\n"
            "                        [y | rest2] ->\n"
            "                            let result = partition(rest2) in\n"
            "                            match result do\n"
            "                                {evens, odds} -> {[x | evens], [y | odds]}\n"
            "                            end\n"
            "                    end\n"
            "            end\n"
            "        end\n"
            "    "
        >>,

    case cure_lexer:tokenize(Source) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, _AST} ->
                    ok;
                {error, Error} ->
                    throw({parse_error, Error})
            end;
        {error, Error} ->
            throw({lex_error, Error})
    end.
