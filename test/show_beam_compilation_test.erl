-module(show_beam_compilation_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").

run() ->
    io:format("~n==== Show Module BEAM Compilation Test ====~n~n"),

    % Test: Compile Show module to actual BEAM file
    io:format("Test 1: Parsing lib/std/show.cure...~n"),
    case cure_parser:parse_file("lib/std/show.cure") of
        {ok, [#module_def{name = ModName, items = Items} = ModuleDef]} ->
            io:format("  ✓ Parsed module ~p~n", [ModName]),

            % Test 2: Type check the module
            io:format("~nTest 2: Type checking...~n"),
            TypeCheckResult = cure_typechecker:check_program([ModuleDef]),

            case get_success(TypeCheckResult) of
                true ->
                    io:format("  ✓ Type checking succeeded~n"),

                    % Test 3: Compile to BEAM
                    io:format("~nTest 3: Compiling to BEAM bytecode...~n"),
                    Options = [],

                    case cure_codegen:compile_module(ModuleDef, Options) of
                        {ok, CompiledModule} ->
                            io:format("  ✓ Module compilation succeeded~n"),
                            io:format("  Compiled module info:~n"),
                            io:format("    Name: ~p~n", [maps:get(name, CompiledModule, undefined)]),
                            io:format("    Functions: ~p~n", [
                                length(maps:get(functions, CompiledModule, []))
                            ]),
                            io:format("    Exports: ~p~n", [
                                length(maps:get(exports, CompiledModule, []))
                            ]),

                            % Test 4: Try to write to BEAM file
                            io:format("~nTest 4: Generating BEAM file...~n"),
                            % Use the module's actual name for the output file
                            ModuleName = maps:get(name, CompiledModule),
                            % Convert module name to safe filename (replace dots with underscores)
                            ModuleNameStr = atom_to_list(ModuleName),
                            SafeModuleName = list_to_atom(
                                lists:flatten(string:replace(ModuleNameStr, ".", "_", all))
                            ),
                            OutputDir = "_build/test/",
                            OutputPath = OutputDir ++ atom_to_list(SafeModuleName) ++ ".beam",
                            filelib:ensure_dir(OutputPath),

                            case cure_codegen:write_beam_module(CompiledModule, OutputPath) of
                                {ok, {ActualModName, _}} ->
                                    io:format("  ✓ BEAM file written to ~s~n", [OutputPath]),
                                    io:format("  ✓ Module name in BEAM: ~p~n", [ActualModName]),

                                    % Test 5: Try to load the module by its internal name
                                    io:format("~nTest 5: Loading compiled module...~n"),
                                    % Since BEAM module name is 'Std.Show' but filename is Std_Show.beam,
                                    % we need to use code:load_binary
                                    case file:read_file(OutputPath) of
                                        {ok, Binary} ->
                                            case
                                                code:load_binary(ActualModName, OutputPath, Binary)
                                            of
                                                {module, LoadedMod} ->
                                                    io:format("  ✓ Module loaded: ~p~n", [LoadedMod]),

                                                    % Test 6: Try to call an instance method
                                                    io:format(
                                                        "~nTest 6: Calling ~p:'Show_Int_show'(42)...~n",
                                                        [LoadedMod]
                                                    ),
                                                    try
                                                        Result = LoadedMod:'Show_Int_show'(42),
                                                        io:format("  ✓ Call succeeded!~n"),
                                                        io:format("  Result: ~p~n", [Result]),
                                                        io:format(
                                                            "~n~n==== ALL TESTS PASSED ====~n~n"
                                                        )
                                                    catch
                                                        Error:Reason:Stack ->
                                                            io:format("  ✗ Call failed: ~p:~p~n", [
                                                                Error, Reason
                                                            ]),
                                                            case os:getenv("CURE_DEBUG") of
                                                                "1" ->
                                                                    io:format("  Stack: ~p~n", [
                                                                        Stack
                                                                    ]);
                                                                _ ->
                                                                    ok
                                                            end,
                                                            io:format(
                                                                "~n~n==== TEST PARTIALLY PASSED ====~n~n"
                                                            )
                                                    end;
                                                {error, LoadReason} ->
                                                    io:format("  ✗ Module load failed: ~p~n", [
                                                        LoadReason
                                                    ]),
                                                    io:format(
                                                        "~n~n==== TEST PARTIALLY PASSED ====~n~n"
                                                    )
                                            end;
                                        {error, ReadReason} ->
                                            io:format("  ✗ Failed to read BEAM file: ~p~n", [
                                                ReadReason
                                            ]),
                                            io:format("~n~n==== TEST PARTIALLY PASSED ====~n~n")
                                    end;
                                {error, WriteReason} ->
                                    io:format("  ✗ BEAM file write failed: ~p~n", [WriteReason]),
                                    io:format("~n~n==== TEST PARTIALLY PASSED ====~n~n")
                            end;
                        {error, CompileReason} ->
                            io:format("  ✗ Compilation failed: ~p~n", [CompileReason]),
                            io:format("~n~n==== TEST FAILED ====~n~n")
                    end;
                false ->
                    io:format("  ✗ Type checking failed~n"),
                    Errors = get_errors(TypeCheckResult),
                    lists:foreach(
                        fun(E) ->
                            io:format("    Error: ~s~n", [element(2, E)])
                        end,
                        lists:sublist(Errors, 3)
                    ),
                    io:format("~n~n==== TEST FAILED ====~n~n")
            end;
        {error, Reason} ->
            io:format("  ✗ Parse error: ~p~n", [Reason]),
            io:format("~n~n==== TEST FAILED ====~n~n")
    end.

% Helper functions
get_success(Result) -> element(2, Result).
get_errors(Result) -> element(4, Result).
