%% End-to-end compilation test for Cure
-module(test_e2e_compilation).
-export([run/0, test_simple_compilation/0]).

-include("src/parser/cure_ast_simple.hrl").

run() ->
    io:format("=== End-to-end Compilation Test ===~n"),
    test_simple_compilation(),
    io:format("All tests completed!~n").

test_simple_compilation() ->
    SourceFile = "examples/simplified/minimal_success.cure",
    
    try
        % Step 1: Lexical analysis
        io:format("1. Lexical analysis...~n"),
        {ok, Tokens} = cure_lexer:tokenize_file(SourceFile),
        io:format("   ✓ Tokens: ~p~n", [length(Tokens)]),
        
        % Step 2: Parsing
        io:format("2. Parsing...~n"),
        case cure_parser:parse(Tokens) of
            {ok, AST} -> 
                io:format("   ✓ Parser successful~n"),
                
                % Step 3: Create proper module structure
                io:format("3. Module structure creation...~n"),
                ModuleAST = create_test_module(AST),
                io:format("   ✓ Module AST created~n"),
                
                % Step 4: Code generation
                io:format("4. Code generation...~n"),
                case cure_codegen:compile_module(ModuleAST) of
                    {ok, Module} -> 
                        io:format("   ✓ Code generation successful~n"),
                        io:format("   Module keys: ~p~n", [maps:keys(Module)]),
                        
                        % Step 5: BEAM file generation
                        io:format("5. BEAM generation...~n"),
                        test_beam_generation(Module);
                    {error, CodegenError} -> 
                        io:format("   ✗ Code generation failed: ~p~n", [CodegenError])
                end;
            {error, ParseError} -> 
                io:format("   ✗ Parser failed: ~p~n", [ParseError])
        end
    catch 
        Error:Reason:Stack ->
            io:format("Exception: ~p:~p~n~p~n", [Error, Reason, Stack])
    end.

%% Create a proper module AST from parsed items
create_test_module(Items) ->
    % Extract function names for exports
    Exports = extract_exports(Items),
    
    % Create module record (using tuple format that codegen expects)
    {module_def, test_module, [], {export_list, Exports, {location, 1, 1, undefined}}, Items, {location, 1, 1, undefined}}.

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

%% Test BEAM generation
test_beam_generation(Module) ->
    try
        % Use module name for BEAM file to avoid loading issues
        ModuleName = maps:get(name, Module, test_module),
        BeamFileName = atom_to_list(ModuleName) ++ ".beam",
        case cure_codegen:generate_beam_file(Module, BeamFileName) of
            {ok, {ModuleName, Path}} -> 
                io:format("   ✓ BEAM generation successful: ~p -> ~s~n", [ModuleName, Path]),
                test_beam_loading(Path);
            {error, BeamError} -> 
                io:format("   ✗ BEAM generation failed: ~p~n", [BeamError])
        end
    catch 
        Error:Reason:Stack ->
            io:format("   ✗ BEAM generation exception: ~p:~p~n~p~n", [Error, Reason, Stack])
    end.

%% Test loading the generated BEAM file
test_beam_loading(BeamPath) ->
    try
        io:format("6. BEAM loading...~n"),
        % Use test_module as the module name since that's what's in the BEAM file
        ModuleName = test_module,
        case code:load_file(ModuleName) of
            {module, LoadedModuleName} ->
                io:format("   ✓ Module loaded successfully: ~p~n", [LoadedModuleName]),
                test_function_execution(LoadedModuleName);
            {error, LoadError} ->
                % Try alternative loading method
                io:format("   Trying alternative loading method...~n"),
                try
                    code:purge(ModuleName),
                    {module, LoadedName} = code:load_abs(filename:rootname(BeamPath)),
                    io:format("   ✓ Module loaded successfully: ~p~n", [LoadedName]),
                    test_function_execution(LoadedName)
                catch
                    _:AlternativeError ->
                        io:format("   ✗ Module loading failed: ~p (alternative: ~p)~n", [LoadError, AlternativeError])
                end
        end
    catch 
        Error:Reason:Stack ->
            io:format("   ✗ Loading exception: ~p:~p~n~p~n", [Error, Reason, Stack])
    end.

%% Test executing the compiled function
test_function_execution(ModuleName) ->
    try
        io:format("7. Function execution...~n"),
        case erlang:function_exported(ModuleName, main, 0) of
            true ->
                Result = ModuleName:main(),
                io:format("   ✓ Function executed successfully: ~p~n", [Result]);
            false ->
                io:format("   ✗ Function 'main/0' not exported~n")
        end
    catch 
        Error:Reason:Stack ->
            io:format("   ✗ Execution exception: ~p:~p~n~p~n", [Error, Reason, Stack])
    end.