-module(test_codegen).
-export([run/0]).

run() ->
    code:add_pathsz(["_build/ebin", "_build/lib"]),
    {ok, Source} = file:read_file("examples/08_typeclasses.cure"),
    {ok, Tokens} = cure_lexer:tokenize(Source),
    {ok, AST} = cure_parser:parse(Tokens),

    io:format("=== CODE GENERATION ===~n"),
    try
        Opts = [{debug_info, true}, {optimize, 1}],
        Result = cure_codegen:compile_program(AST, Opts),
        io:format("Codegen result: ~p~n", [Result]),
        Result
    catch
        Class:Error:Stack ->
            io:format("CODEGEN EXCEPTION: ~p:~p~n", [Class, Error]),
            io:format("Stack:~n"),
            [io:format("  ~p~n", [Frame]) || Frame <- Stack],
            {error, Class, Error}
    end.
