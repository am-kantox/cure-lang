-module(show_module_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").

% Helper to access typecheck result fields
get_success(Result) -> element(2, Result).
get_errors(Result) -> element(4, Result).
get_error_message(Error) -> element(2, Error).
get_error_location(Error) -> element(3, Error).
get_error_details(Error) -> element(4, Error).

run() ->
    io:format("~n==== Show Module Parse & Typecheck Test ====~n~n"),

    % Test 1: Parse the Show module
    io:format("Test 1: Parsing lib/std/show.cure...~n"),
    case cure_parser:parse_file("lib/std/show.cure") of
        {ok, AST} ->
            io:format("  ✓ Successfully parsed~n"),
            io:format("  AST has ~p top-level items~n", [length(AST)]),

            % Extract module definition
            case AST of
                [#module_def{name = Name, items = Items}] ->
                    io:format("  Module name: ~p~n", [Name]),
                    io:format("  Module has ~p items~n", [length(Items)]),

                    % Count typeclasses and instances
                    Typeclasses = [I || I <- Items, is_record(I, typeclass_def)],
                    Instances = [I || I <- Items, is_record(I, instance_def)],
                    Functions = [I || I <- Items, is_record(I, function_def)],

                    io:format("  - ~p typeclass definitions~n", [length(Typeclasses)]),
                    io:format("  - ~p instance definitions~n", [length(Instances)]),
                    io:format("  - ~p function definitions~n", [length(Functions)]),

                    % Show typeclass names
                    TypeclassNames = [TC#typeclass_def.name || TC <- Typeclasses],
                    io:format("  Typeclasses: ~p~n", [TypeclassNames]),

                    % Show instance types
                    InstanceTypes = [
                        {I#instance_def.typeclass, I#instance_def.type_args}
                     || I <- Instances
                    ],
                    io:format("  Instances: ~p~n", [InstanceTypes]),

                    % Test 2: Type check the Show module
                    io:format("~nTest 2: Type checking lib/std/show.cure...~n"),
                    Result = cure_typechecker:check_program(AST),
                    case get_success(Result) of
                        true ->
                            io:format("  ✓ Type checking succeeded~n"),

                            % Test 3: Parse and type check show_test.cure
                            io:format("~nTest 3: Parsing examples/show_test.cure...~n"),
                            case cure_parser:parse_file("examples/show_test.cure") of
                                {ok, TestAST} ->
                                    io:format("  ✓ Successfully parsed~n"),

                                    % TODO: We need to somehow provide the Show module to the type checker
                                    % For now, just check that show_test parses
                                    io:format(
                                        "~nTest 3b: Type checking examples/show_test.cure...~n"
                                    ),
                                    TestResult = cure_typechecker:check_program(TestAST),
                                    case get_success(TestResult) of
                                        true ->
                                            io:format("  ✓ Type checking succeeded~n"),
                                            io:format("~n~n==== ALL TESTS PASSED ====~n~n");
                                        false ->
                                            io:format("  ✗ Type checking failed~n"),
                                            Errors = get_errors(TestResult),
                                            lists:foreach(
                                                fun(E) ->
                                                    io:format("    Error: ~s~n", [
                                                        get_error_message(E)
                                                    ]),
                                                    io:format("    Details: ~p~n", [
                                                        get_error_details(E)
                                                    ])
                                                end,
                                                Errors
                                            ),
                                            io:format("~n~n==== SOME TESTS FAILED ====~n~n")
                                    end;
                                {error, ParseError} ->
                                    io:format("  ✗ Parse error: ~p~n", [ParseError]),
                                    io:format("~n~n==== TESTS FAILED ====~n~n")
                            end;
                        false ->
                            io:format("  ✗ Type checking failed~n"),
                            Errors = get_errors(Result),
                            lists:foreach(
                                fun(E) ->
                                    io:format("    Error: ~s~n", [get_error_message(E)]),
                                    io:format("    Location: ~p~n", [get_error_location(E)]),
                                    io:format("    Details: ~p~n", [get_error_details(E)])
                                end,
                                Errors
                            ),
                            io:format("~n~n==== TESTS FAILED ====~n~n")
                    end;
                _ ->
                    io:format("  ✗ Unexpected AST structure~n"),
                    io:format("~n~n==== TESTS FAILED ====~n~n")
            end;
        {error, Reason} ->
            io:format("  ✗ Parse error: ~p~n", [Reason]),
            io:format("~n~n==== TESTS FAILED ====~n~n")
    end.
