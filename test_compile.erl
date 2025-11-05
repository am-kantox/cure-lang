-module(test_compile).
-export([run/0]).

run() ->
    code:add_pathsz(["_build/ebin", "_build/lib"]),
    Result = cure_cli:compile_file("examples/08_typeclasses.cure"),
    io:format("~nResult: ~p~n", [Result]),
    Result.
