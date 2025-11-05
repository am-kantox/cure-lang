-module(test_typeclass_compile).
-export([test/0]).

test() ->
    code:add_pathsz(["_build/ebin", "_build/lib"]),
    try
        Result = cure_cli:compile_file("examples/08_typeclasses.cure"),
        io:format("Result: ~p~n", [Result]),
        Result
    catch
        Class:Error:Stack ->
            io:format("EXCEPTION ~p:~p~n", [Class, Error]),
            io:format("Stack: ~p~n", [Stack]),
            {caught, Class, Error}
    end.
