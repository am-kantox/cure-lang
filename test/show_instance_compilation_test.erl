-module(show_instance_compilation_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").

run() ->
    io:format("~n==== Show Instance Compilation Test ====~n~n"),

    % Test: Parse Show module and verify instance structure
    io:format("Test 1: Parsing lib/std/show.cure and checking instances...~n"),
    case cure_parser:parse_file("lib/std/show.cure") of
        {ok, [#module_def{name = ModName, items = Items}]} ->
            io:format("  ✓ Parsed module ~p~n", [ModName]),

            % Extract instances
            Instances = [I || I <- Items, is_record(I, instance_def)],
            io:format("  Found ~p instance definitions~n", [length(Instances)]),

            % Check each instance has methods
            lists:foreach(
                fun(Instance) ->
                    #instance_def{
                        typeclass = TC,
                        type_args = Types,
                        methods = Methods
                    } = Instance,

                    TypeNames = extract_type_names(Types),
                    io:format("  Instance ~p(~p): ~p methods~n", [
                        TC, TypeNames, length(Methods)
                    ]),

                    % Show method names
                    MethodNames = [M#function_def.name || M <- Methods],
                    io:format("    Methods: ~p~n", [MethodNames])
                end,
                Instances
            ),

            % Test 2: Try to compile the instances
            io:format("~nTest 2: Attempting to compile Show module...~n"),

            % Type check first
            TypeCheckResult = cure_typechecker:check_program([
                #module_def{
                    name = ModName,
                    exports = [],
                    items = Items,
                    location = undefined
                }
            ]),

            case get_success(TypeCheckResult) of
                true ->
                    io:format("  ✓ Type checking succeeded~n"),

                    % Now try codegen
                    io:format("~nTest 3: Generating code for instances...~n"),

                    % Create default options as a proplist
                    Options = [],

                    % Try to compile the module (pass module directly, not in a list)
                    case
                        cure_codegen:compile_module(
                            #module_def{
                                name = 'Std.Show',
                                exports = [],
                                items = Items,
                                location = undefined
                            },
                            Options
                        )
                    of
                        {ok, CompiledModule} ->
                            io:format("  ✓ Codegen succeeded~n"),

                            % Check what functions were generated
                            Functions = maps:get(functions, CompiledModule, []),
                            io:format("  Generated ~p functions~n", [length(Functions)]),

                            % Look for instance methods
                            InstanceFuncs = [
                                F
                             || F <- Functions,
                                is_map(F),
                                case maps:get(name, F, undefined) of
                                    N when is_atom(N) ->
                                        Str = atom_to_list(N),
                                        string:find(Str, "Show_") =/= nomatch;
                                    _ ->
                                        false
                                end
                            ],

                            io:format("  Found ~p instance methods~n", [length(InstanceFuncs)]),

                            lists:foreach(
                                fun(F) ->
                                    case maps:get(name, F, undefined) of
                                        undefined ->
                                            ok;
                                        Name ->
                                            Arity = maps:get(arity, F, 0),
                                            io:format("    - ~p/~p~n", [Name, Arity])
                                    end
                                end,
                                InstanceFuncs
                            ),

                            case length(InstanceFuncs) > 0 of
                                true ->
                                    io:format("~n  ✓ Instance methods were generated!~n"),
                                    io:format("~n~n==== TEST PASSED ====~n~n");
                                false ->
                                    io:format("~n  ✗ No instance methods found~n"),
                                    io:format("     This might indicate codegen needs work~n"),
                                    io:format("~n~n==== TEST PARTIALLY PASSED ====~n~n")
                            end;
                        {error, CodegenReason} ->
                            io:format("  ✗ Codegen failed: ~p~n", [CodegenReason]),
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

extract_type_names([]) -> [];
extract_type_names([#primitive_type{name = Name} | Rest]) -> [Name | extract_type_names(Rest)];
extract_type_names([#dependent_type{name = Name} | Rest]) -> [Name | extract_type_names(Rest)];
extract_type_names([_ | Rest]) -> extract_type_names(Rest).
