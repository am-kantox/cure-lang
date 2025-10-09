#!/usr/bin/env escript

main(_) ->
    code:add_path("_build/ebin"),
    {ok, AST} = cure_parser:parse_file("test_fresh_match.cure"),
    io:format("Parse successful, AST length: ~w~n", [length(AST)]),

    case cure_codegen:compile_program(AST) of
        {ok, Modules} ->
            io:format("SUCCESS: Compiled ~w modules!~n", [length(Modules)]),
            lists:foreach(
                fun(Module) ->
                    case Module of
                        {function, FunctionData} ->
                            Name = maps:get(name, FunctionData),
                            Arity = maps:get(arity, FunctionData),
                            io:format("  Function: ~w/~w~n", [Name, Arity]);
                        ModuleMap when is_map(ModuleMap) ->
                            ModuleName = maps:get(name, ModuleMap),
                            Functions = maps:get(functions, ModuleMap),
                            io:format("  Module: ~w with ~w functions~n", [
                                ModuleName, length(Functions)
                            ]);
                        _ ->
                            io:format("  Other: ~p~n", [Module])
                    end
                end,
                Modules
            );
        {error, Error} ->
            io:format("ERROR: ~p~n", [Error])
    end.
