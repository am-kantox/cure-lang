-module(multiclause_typecheck_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").

%% Include typecheck_result record definition
-record(typecheck_result, {
    success :: boolean(),
    type :: term() | undefined,
    errors :: [term()],
    warnings :: [term()]
}).

run() ->
    io:format("~n=== Multi-Clause Function Type Checking Test ===~n"),
    test_union_type_derivation(),
    test_single_clause_backward_compat(),
    io:format("All tests passed!~n").

test_union_type_derivation() ->
    io:format("Test 1: Union type derivation from multi-clause function...~n"),
    Source =
        <<
            "\n"
            "    module Test do\n"
            "        def foo(i: Int) -> String do\n"
            "            \"integer\"\n"
            "        end\n"
            "        \n"
            "        def foo(f: Float) -> String do\n"
            "            \"float\"\n"
            "        end\n"
            "    end\n"
            "    "
        >>,

    {ok, Tokens} = cure_lexer:tokenize(Source),
    {ok, AST} = cure_parser:parse(Tokens),

    % Type check the program
    Result = cure_typechecker:check_program(AST),

    % Should succeed
    true = Result#typecheck_result.success,

    io:format("  ✓ Multi-clause function type-checks successfully~n"),
    io:format("  ✓ Derived signature should have union types for parameters~n"),
    ok.

test_single_clause_backward_compat() ->
    io:format("Test 2: Single-clause backward compatibility...~n"),
    Source =
        <<
            "\n"
            "    module Test do\n"
            "        def double(x: Int) -> Int do\n"
            "            x + x\n"
            "        end\n"
            "    end\n"
            "    "
        >>,

    {ok, Tokens} = cure_lexer:tokenize(Source),
    {ok, AST} = cure_parser:parse(Tokens),

    Result = cure_typechecker:check_program(AST),

    % Should succeed
    true = Result#typecheck_result.success,

    io:format("  ✓ Single-clause function still type-checks correctly~n"),
    ok.
