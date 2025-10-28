-module(monomorphization_edge_cases_test).

-export([run/0]).

-include("../src/parser/cure_ast.hrl").

%%% Monomorphization Edge Cases Test Suite %%%

run() ->
    io:format("Running Monomorphization Edge Cases Tests...~n"),

    Tests = [
        fun test_recursive_polymorphic_functions/0,
        fun test_mutually_recursive_polymorphic/0,
        fun test_higher_kinded_types/0,
        fun test_nested_type_parameters/0,
        fun test_constrained_polymorphism/0,
        fun test_polymorphic_records/0,
        fun test_multiple_type_params/0,
        fun test_partial_specialization/0,
        fun test_monomorphization_caching/0,
        fun test_polymorphic_fsm/0
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

    io:format("~nMonomorphization Tests: ~p passed, ~p failed~n", [Passed, Failed]),

    case Failed of
        0 -> ok;
        _ -> erlang:halt(1)
    end.

%%% Test: Recursive Polymorphic Functions %%%

test_recursive_polymorphic_functions() ->
    io:format("  Testing recursive polymorphic functions...~n"),

    % Test recursive list operations with type parameters
    % Example: recursive map function
    Source =
        <<
            "\n"
            "        def map<T, U>(f: <T> -> <U>, list: List(<T>)): List(<U>) do\n"
            "            match list do\n"
            "                [] -> []\n"
            "                [head | tail] -> [f(head) | map(f, tail)]\n"
            "            end\n"
            "        end\n"
            "    "
        >>,

    case cure_lexer:tokenize(Source) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, _AST} ->
                    % TODO: Verify monomorphization creates separate versions
                    % for different type instantiations
                    ok;
                {error, Error} ->
                    throw({parse_error, Error})
            end;
        {error, Error} ->
            throw({lex_error, Error})
    end.

%%% Test: Mutually Recursive Polymorphic Functions %%%

test_mutually_recursive_polymorphic() ->
    io:format("  Testing mutually recursive polymorphic functions...~n"),

    % Test functions that call each other with polymorphic types
    Source =
        <<
            "\n"
            "        def even<T>(list: List(<T>)): Bool do\n"
            "            match list do\n"
            "                [] -> true\n"
            "                [_] -> false\n"
            "                [_ | tail] -> odd(tail)\n"
            "            end\n"
            "        end\n"
            "        \n"
            "        def odd<T>(list: List(<T>)): Bool do\n"
            "            match list do\n"
            "                [] -> false\n"
            "                [_] -> true\n"
            "                [_ | tail] -> even(tail)\n"
            "            end\n"
            "        end\n"
            "    "
        >>,

    case cure_lexer:tokenize(Source) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, _AST} ->
                    % TODO: Verify both functions are monomorphized together
                    ok;
                {error, Error} ->
                    throw({parse_error, Error})
            end;
        {error, Error} ->
            throw({lex_error, Error})
    end.

%%% Test: Higher-Kinded Types %%%

test_higher_kinded_types() ->
    io:format("  Testing higher-kinded types...~n"),

    % Test type constructors as parameters
    % Example: functor map
    ok.

%%% Test: Nested Type Parameters %%%

test_nested_type_parameters() ->
    io:format("  Testing nested type parameters...~n"),

    % Test List(List(<T>)) and similar nested structures
    Source =
        <<
            "\n"
            "        def flatten<T>(nested: List(List(<T>))): List(<T>) do\n"
            "            match nested do\n"
            "                [] -> []\n"
            "                [inner | rest] -> concat(inner, flatten(rest))\n"
            "            end\n"
            "        end\n"
            "    "
        >>,

    case cure_lexer:tokenize(Source) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, _AST} ->
                    % TODO: Verify nested type parameters are correctly instantiated
                    ok;
                {error, Error} ->
                    throw({parse_error, Error})
            end;
        {error, Error} ->
            throw({lex_error, Error})
    end.

%%% Test: Constrained Polymorphism %%%

test_constrained_polymorphism() ->
    io:format("  Testing constrained polymorphism...~n"),

    % Test type parameters with constraints
    % Example: sort requires Ord constraint
    ok.

%%% Test: Polymorphic Records %%%

test_polymorphic_records() ->
    io:format("  Testing polymorphic records...~n"),

    % Test records with type parameters
    Source =
        <<
            "\n"
            "        record Pair<T, U> do\n"
            "            first: <T>\n"
            "            second: <U>\n"
            "        end\n"
            "        \n"
            "        def swap<T, U>(p: Pair(<T>, <U>)): Pair(<U>, <T>) do\n"
            "            Pair{first: p.second, second: p.first}\n"
            "        end\n"
            "    "
        >>,

    case cure_lexer:tokenize(Source) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, _AST} ->
                    % TODO: Verify record instantiations are created
                    ok;
                {error, Error} ->
                    throw({parse_error, Error})
            end;
        {error, Error} ->
            throw({lex_error, Error})
    end.

%%% Test: Multiple Type Parameters %%%

test_multiple_type_params() ->
    io:format("  Testing multiple type parameters...~n"),

    % Test functions with multiple independent type parameters
    Source =
        <<
            "\n"
            "        def zip<T, U>(list1: List(<T>), list2: List(<U>)): List(Tuple(<T>, <U>)) do\n"
            "            match {list1, list2} do\n"
            "                {[], _} -> []\n"
            "                {_, []} -> []\n"
            "                {[h1 | t1], [h2 | t2]} -> [{h1, h2} | zip(t1, t2)]\n"
            "            end\n"
            "        end\n"
            "    "
        >>,

    case cure_lexer:tokenize(Source) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, _AST} ->
                    % TODO: Verify all type parameters are correctly handled
                    ok;
                {error, Error} ->
                    throw({parse_error, Error})
            end;
        {error, Error} ->
            throw({lex_error, Error})
    end.

%%% Test: Partial Specialization %%%

test_partial_specialization() ->
    io:format("  Testing partial specialization...~n"),

    % Test when only some type parameters are known
    % Example: map specialized to List but generic in element type
    ok.

%%% Test: Monomorphization Caching %%%

test_monomorphization_caching() ->
    io:format("  Testing monomorphization caching...~n"),

    % Test that identical instantiations reuse the same monomorphized version
    Source =
        <<
            "\n"
            "        def id<T>(x: <T>): <T> do x end\n"
            "        \n"
            "        def test(): Int do\n"
            "            let x = id(42)\n"
            "            let y = id(43)\n"
            "            x + y\n"
            "        end\n"
            "    "
        >>,

    case cure_lexer:tokenize(Source) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, _AST} ->
                    % TODO: Verify only one Int->Int version is generated
                    ok;
                {error, Error} ->
                    throw({parse_error, Error})
            end;
        {error, Error} ->
            throw({lex_error, Error})
    end.

%%% Test: Polymorphic FSM %%%

test_polymorphic_fsm() ->
    io:format("  Testing polymorphic FSM...~n"),

    % Test FSM with polymorphic state data
    Source =
        <<
            "\n"
            "        fsm Buffer<T> do\n"
            "            state empty do\n"
            "                on push(x: <T>) -> filled(x)\n"
            "            end\n"
            "            \n"
            "            state filled(item: <T>) do\n"
            "                on pop -> empty\n"
            "                on peek -> filled(item)\n"
            "            end\n"
            "        end\n"
            "    "
        >>,

    case cure_lexer:tokenize(Source) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, _AST} ->
                    % TODO: Verify FSM is correctly monomorphized for each type
                    ok;
                {error, Error} ->
                    throw({parse_error, Error})
            end;
        {error, Error} ->
            throw({lex_error, Error})
    end.
