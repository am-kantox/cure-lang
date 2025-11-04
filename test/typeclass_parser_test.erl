-module(typeclass_parser_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").

run() ->
    io:format("~n=== Type Class Parser Tests ===~n~n"),

    test_typeclass_definition(),
    test_instance_definition(),
    test_derive_clause(),

    io:format("~n=== All Typeclass Parser Tests Passed ===~n").

test_typeclass_definition() ->
    io:format("Testing typeclass definition parsing...~n"),

    Source =
        <<
            "\n"
            "        typeclass Show(T) do\n"
            "          def show(x: T): String\n"
            "        end\n"
            "    "
        >>,

    case cure_lexer:scan(Source) of
        {ok, Tokens} ->
            io:format("  Tokens: ~p~n", [length(Tokens)]),
            case cure_parser:parse(Tokens) of
                {ok, AST} ->
                    io:format("  ✓ Successfully parsed typeclass definition~n"),
                    case AST of
                        [#typeclass_def{name = 'Show'}] ->
                            io:format("  ✓ Typeclass name is correct~n");
                        _ ->
                            io:format("  AST: ~p~n", [AST]),
                            throw({error, unexpected_ast})
                    end;
                {error, Reason} ->
                    io:format("  ✗ Parse error: ~p~n", [Reason]),
                    throw({error, parse_failed})
            end;
        {error, Reason} ->
            io:format("  ✗ Lexer error: ~p~n", [Reason]),
            throw({error, lexer_failed})
    end.

test_instance_definition() ->
    io:format("~nTesting instance definition parsing...~n"),

    Source =
        <<
            "\n"
            "        instance Show(Int) do\n"
            "          def show(x: Int): String = \"42\"\n"
            "        end\n"
            "    "
        >>,

    case cure_lexer:scan(Source) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, AST} ->
                    io:format("  ✓ Successfully parsed instance definition~n"),
                    case AST of
                        [#instance_def{typeclass = 'Show'}] ->
                            io:format("  ✓ Instance typeclass is correct~n");
                        _ ->
                            io:format("  AST: ~p~n", [AST]),
                            throw({error, unexpected_ast})
                    end;
                {error, Reason} ->
                    io:format("  ✗ Parse error: ~p~n", [Reason]),
                    throw({error, parse_failed})
            end;
        {error, Reason} ->
            io:format("  ✗ Lexer error: ~p~n", [Reason]),
            throw({error, lexer_failed})
    end.

test_derive_clause() ->
    io:format("~nTesting derive clause parsing...~n"),

    Source =
        <<
            "\n"
            "        derive Show for Person\n"
            "    "
        >>,

    case cure_lexer:scan(Source) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, AST} ->
                    io:format("  ✓ Successfully parsed derive clause~n"),
                    case AST of
                        [#derive_clause{typeclass = 'Show'}] ->
                            io:format("  ✓ Derive typeclass is correct~n");
                        _ ->
                            io:format("  AST: ~p~n", [AST]),
                            throw({error, unexpected_ast})
                    end;
                {error, Reason} ->
                    io:format("  ✗ Parse error: ~p~n", [Reason]),
                    throw({error, parse_failed})
            end;
        {error, Reason} ->
            io:format("  ✗ Lexer error: ~p~n", [Reason]),
            throw({error, lexer_failed})
    end.
