-module(check_exports).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").

run() ->
    {ok, [ModDef]} = cure_parser:parse_file("lib/std/show.cure"),
    {ok, Compiled} = cure_codegen:compile_module(ModDef, []),

    io:format("Exports: ~p~n", [maps:get(exports, Compiled)]),
    io:format("~nFunctions (~p total):~n", [length(maps:get(functions, Compiled))]),

    Functions = maps:get(functions, Compiled),
    lists:foreach(
        fun
            (F) when is_map(F) ->
                Name = maps:get(name, F, noname),
                Arity = maps:get(arity, F, 0),
                IsInstance = maps:get(is_instance_method, F, false),
                io:format("  ~p/~p ~s~n", [
                    Name,
                    Arity,
                    case IsInstance of
                        true -> "(instance)";
                        false -> ""
                    end
                ]);
            (_) ->
                ok
        end,
        Functions
    ),

    init:stop().
