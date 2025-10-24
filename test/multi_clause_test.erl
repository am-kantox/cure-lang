-module(multi_clause_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").

run() ->
    io:format("~n=== Multi-Clause Function Test ===~n"),
    test_parse_multi_clause(),
    test_single_clause_backward_compat(),
    io:format("All tests passed!~n").

test_parse_multi_clause() ->
    io:format("Test 1: Parsing multi-clause function...~n"),
    Source =
        <<
            "\n"
            "    module Test do\n"
            "        def foo(i: Int) -> String do\n"
            "            \"integer\"\n"
            "        end\n"
            "        \n"
            "        def foo(n: Nat) -> String do\n"
            "            \"natural\"\n"
            "        end\n"
            "    end\n"
            "    "
        >>,
    {ok, Tokens} = cure_lexer:tokenize(Source),
    {ok, AST} = cure_parser:parse(Tokens),

    % Extract the module
    [Module] = AST,
    #module_def{items = Items} = Module,

    % Find the foo function
    FooFunc = lists:keyfind(foo, #function_def.name, Items),
    #function_def{name = foo, clauses = Clauses} = FooFunc,

    % Should have 2 clauses
    2 = length(Clauses),

    % Check first clause
    [Clause1, Clause2] = Clauses,
    #function_clause{params = Params1} = Clause1,
    1 = length(Params1),

    #function_clause{params = Params2} = Clause2,
    1 = length(Params2),

    io:format("  ✓ Multi-clause function parsed with 2 clauses~n"),
    ok.

test_single_clause_backward_compat() ->
    io:format("Test 2: Single clause backward compatibility...~n"),
    Source =
        <<
            "\n"
            "    module Test do\n"
            "        def bar(x: Int) -> Int do\n"
            "            x + 1\n"
            "        end\n"
            "    end\n"
            "    "
        >>,
    {ok, Tokens} = cure_lexer:tokenize(Source),
    {ok, AST} = cure_parser:parse(Tokens),

    [Module] = AST,
    #module_def{items = Items} = Module,

    BarFunc = lists:keyfind(bar, #function_def.name, Items),
    #function_def{name = bar, clauses = Clauses, params = DeprecatedParams} = BarFunc,

    % Should have 1 clause
    1 = length(Clauses),

    % Deprecated params field should still be populated for backward compat
    true = (DeprecatedParams =/= undefined),

    io:format("  ✓ Single clause maintains backward compatibility~n"),
    ok.
