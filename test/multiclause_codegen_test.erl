-module(multiclause_codegen_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").

run() ->
    io:format("=== Multi-Clause Function Code Generation Test ===~n"),

    % Create a multi-clause function: foo(i: Int) -> String and foo(f: Float) -> String
    io:format("Test 1: Testing multi-clause codegen...~n"),

    Code =
        <<
            "\n"
            "        module Test do\n"
            "            def foo(i: Int) -> String do\n"
            "                \"integer\"\n"
            "            end\n"
            "            \n"
            "            def foo(f: Float) -> String do\n"
            "                \"float\"\n"
            "            end\n"
            "        end\n"
            "    "
        >>,

    % Tokenize and parse
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    % Compile module
    case cure_codegen:compile_module(hd(AST)) of
        {ok, CompiledModule} ->
            io:format("  ✓ Module compiled successfully~n"),

            % Check that functions list contains the multi-clause function
            Functions = maps:get(functions, CompiledModule),
            io:format("  Functions count: ~p~n", [length(Functions)]),

            % Find the foo function
            case
                lists:search(
                    fun
                        (F) when is_map(F) ->
                            maps:get(name, F, undefined) =:= foo;
                        (_) ->
                            false
                    end,
                    Functions
                )
            of
                {value, FooFunc} ->
                    io:format("  ✓ Found foo function~n"),
                    case maps:get(is_multiclause, FooFunc, false) of
                        true ->
                            io:format("  ✓ Function is marked as multi-clause~n"),
                            Clauses = maps:get(clauses, FooFunc, []),
                            io:format("  Clause count: ~p~n", [length(Clauses)]),
                            case length(Clauses) of
                                2 ->
                                    io:format("  ✓ Both clauses present~n");
                                N ->
                                    io:format("  ✗ Expected 2 clauses, got ~p~n", [N])
                            end;
                        false ->
                            io:format("  ✗ Function is NOT marked as multi-clause~n")
                    end;
                false ->
                    io:format("  ✗ foo function not found~n")
            end;
        {error, Reason} ->
            io:format("  ✗ Compilation failed: ~p~n", [Reason])
    end,

    io:format("~nAll tests passed!~n").
