-module(test_direct).
-export([run/0]).

run() ->
    code:add_pathsz(["_build/ebin", "_build/lib"]),
    {ok, Source} = file:read_file("examples/08_typeclasses.cure"),
    io:format("=== LEXING ===~n"),
    {ok, Tokens} = cure_lexer:tokenize(Source),
    io:format("Tokens: ~p~n", [length(Tokens)]),

    io:format("~n=== PARSING ===~n"),
    {ok, AST} = cure_parser:parse(Tokens),
    io:format("AST parsed~n"),

    io:format("~n=== TYPE CHECKING ===~n"),
    try
        Result = cure_typechecker:check_program(AST),
        io:format("Type check result: ~p~n", [Result]),
        Result
    catch
        Class:Error:Stack ->
            io:format("TYPE CHECK EXCEPTION: ~p:~p~n", [Class, Error]),
            io:format("Stack:~n"),
            [io:format("  ~p~n", [Frame]) || Frame <- Stack],
            {error, Class, Error}
    end.
