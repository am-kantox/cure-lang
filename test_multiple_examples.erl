-module(test_multiple_examples).
-export([run/0, test_example/1]).

run() ->
    io:format("=== Testing Multiple Cure Examples ===~n"),
    Examples = [
        "examples/simplified/minimal_success.cure",
        "examples/simplified/basic_types_demo.cure",
        "examples/simplified/test_operators.cure"
    ],
    test_examples(Examples, 1).

test_examples([], _Counter) ->
    io:format("All example tests completed!~n");
test_examples([Example | Rest], Counter) ->
    test_example_with_counter(Example, Counter),
    test_examples(Rest, Counter + 1).

test_example_with_counter(File, Counter) ->
    ModuleName = list_to_atom("test_module_" ++ integer_to_list(Counter)),
    io:format("Testing ~s (as ~p)...~n", [File, ModuleName]),
    try
        {ok, Tokens} = cure_lexer:tokenize_file(File),
        {ok, AST} = cure_parser:parse(Tokens),

        % Extract exports
        Exports = extract_exports(AST),

        % Create module
        ModuleAST =
            {module_def, ModuleName, [], {export_list, Exports, {location, 1, 1, undefined}}, AST,
                {location, 1, 1, undefined}},
        {ok, Module} = cure_codegen:compile_module(ModuleAST),

        BeamFile = atom_to_list(ModuleName) ++ ".beam",
        {ok, {_ModName, _Path}} = cure_codegen:generate_beam_file(Module, BeamFile),
        {module, LoadedMod} = code:load_file(ModuleName),

        % Try to run main/0 if it exists
        case erlang:function_exported(LoadedMod, main, 0) of
            true ->
                Result = LoadedMod:main(),
                io:format("   ✓ ~s -> Result: ~p~n", [File, Result]);
            false ->
                io:format("   ✓ ~s -> Compiled successfully (no main/0 function)~n", [File])
        end
    catch
        Error:Reason:Stack ->
            io:format("   ✗ ~s -> Error: ~p:~p~n", [File, Error, Reason])
    end.

test_example(File) ->
    test_example_with_counter(File, 999).

%% Extract exports from function definitions
extract_exports(Items) ->
    extract_exports(Items, []).

extract_exports([], Acc) ->
    lists:reverse(Acc);
extract_exports([{function_def, Name, Params, _RetType, _Constraint, _Body, Location} | Rest], Acc) ->
    Arity = length(Params),
    Export = {export_spec, Name, Arity, Location},
    extract_exports(Rest, [Export | Acc]);
extract_exports([_ | Rest], Acc) ->
    extract_exports(Rest, Acc).
