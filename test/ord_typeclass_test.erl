-module(ord_typeclass_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").

run() ->
    io:format("~n==== Ord Typeclass Test ====~n~n"),

    % Test 1: Parse Ord module
    io:format("Test 1: Parsing lib/std/ord.cure...~n"),
    case cure_parser:parse_file("lib/std/ord.cure") of
        {ok, [#module_def{name = ModName, items = Items}]} ->
            io:format("  ✓ Parsed module ~p~n", [ModName]),

            % Count typeclasses and instances
            Typeclasses = [TC || TC <- Items, is_record(TC, typeclass_def)],
            Instances = [I || I <- Items, is_record(I, instance_def)],
            Functions = [F || F <- Items, is_record(F, function_def)],

            io:format("  Found ~p typeclass definition(s)~n", [length(Typeclasses)]),
            io:format("  Found ~p instance definition(s)~n", [length(Instances)]),
            io:format("  Found ~p helper function(s)~n", [length(Functions)]),

            % Check typeclass definition
            case Typeclasses of
                [#typeclass_def{name = TCName, methods = Methods}] ->
                    io:format("  Typeclass name: ~p~n", [TCName]),
                    io:format("  Methods: ~p~n", [length(Methods)]),

                    MethodNames = [M#method_signature.name || M <- Methods],
                    io:format("  Method names: ~p~n", [MethodNames]);
                _ ->
                    io:format("  Warning: Expected 1 typeclass, got ~p~n", [length(Typeclasses)])
            end,

            % Test 2: Type check
            io:format("~nTest 2: Type checking...~n"),
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

                    % Test 3: Compile
                    io:format("~nTest 3: Compiling module...~n"),
                    case
                        cure_codegen:compile_module(
                            #module_def{
                                name = ModName,
                                exports = [],
                                items = Items,
                                location = undefined
                            },
                            []
                        )
                    of
                        {ok, CompiledModule} ->
                            io:format("  ✓ Compilation succeeded~n"),

                            AllFunctions = maps:get(functions, CompiledModule, []),
                            io:format("  Generated ~p functions~n", [length(AllFunctions)]),

                            % Look for instance methods (Ord_Type_compare)
                            InstanceFuncs = [
                                F
                             || F <- AllFunctions,
                                is_map(F),
                                case maps:get(name, F, undefined) of
                                    N when is_atom(N) ->
                                        Str = atom_to_list(N),
                                        string:find(Str, "Ord_") =/= nomatch andalso
                                            string:find(Str, "_compare") =/= nomatch;
                                    _ ->
                                        false
                                end
                            ],

                            io:format("  Found ~p Ord instance methods~n", [length(InstanceFuncs)]),

                            % List instance methods
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

                            % Look for helper functions
                            HelperFuncs = [
                                F
                             || F <- AllFunctions,
                                is_map(F),
                                case maps:get(name, F, undefined) of
                                    N when is_atom(N) ->
                                        lists:member(N, [lt, le, gt, ge, max, min]);
                                    _ ->
                                        false
                                end
                            ],

                            io:format("  Found ~p helper functions~n", [length(HelperFuncs)]),

                            % Check exports
                            Exports = maps:get(exports, CompiledModule, []),
                            OrdExports = [
                                E
                             || E = {Name, _} <- Exports,
                                begin
                                    NameStr = atom_to_list(Name),
                                    string:find(NameStr, "Ord_") =/= nomatch
                                end
                            ],

                            io:format("~n  Ord instance exports: ~p~n", [length(OrdExports)]),

                            case length(InstanceFuncs) > 0 andalso length(OrdExports) > 0 of
                                true ->
                                    io:format("~n  ✓ Instance methods compiled and exported!~n"),
                                    io:format("~n~n==== TEST PASSED ====~n~n");
                                false ->
                                    io:format("~n  ✗ Missing instance methods or exports~n"),
                                    io:format("~n~n==== TEST FAILED ====~n~n")
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
                            io:format("    Error: ~p~n", [E])
                        end,
                        lists:sublist(Errors, 5)
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
