-module(typeclass_method_resolution_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").

run() ->
    io:format("~n==== Typeclass Method Resolution Test ====~n~n"),

    % Test 1: Parse show_test.cure WITH import
    io:format("Test 1: Type checking show_test.cure WITH import from Std.Show...~n"),
    case cure_parser:parse_file("examples/show_test.cure") of
        {ok, [#module_def{} = Module1]} ->
            Result1 = cure_typechecker:check_program([Module1]),
            case get_success(Result1) of
                true ->
                    io:format("  ✓ Type checking succeeded WITH import~n");
                false ->
                    io:format("  ✗ Type checking FAILED WITH import~n"),
                    print_errors(Result1)
            end;
        {error, Reason1} ->
            io:format("  ✗ Parse error: ~p~n", [Reason1])
    end,

    % Test 2: Create a test WITHOUT import (should fail with unbound_variable)
    io:format("~nTest 2: Creating temporary file without import...~n"),
    NoImportFile = "/tmp/test_no_import.cure",
    NoImportCode =
        "# No Import Test\n"
        "module TestNoImport do\n"
        "  export [test/0]\n"
        "  \n"
        "  def test(): String =\n"
        "    show(42)\n"
        "end\n",
    file:write_file(NoImportFile, NoImportCode),
    io:format("  Type checking show usage WITHOUT import (should fail)...~n"),
    case cure_parser:parse_file(NoImportFile) of
        {ok, AST2} ->
            Result2 = cure_typechecker:check_program(AST2),
            case get_success(Result2) of
                false ->
                    io:format("  ✓ Type checking correctly FAILED without import~n"),
                    % Check if it's the expected unbound_variable error
                    Errors2 = get_errors(Result2),
                    case check_for_unbound_variable(Errors2, show) of
                        true ->
                            io:format("    ✓ Got expected 'unbound_variable: show' error~n");
                        false ->
                            io:format("    ✗ Got different error (not unbound_variable: show)~n"),
                            print_errors(Result2)
                    end;
                true ->
                    io:format("  ✗ Type checking unexpectedly SUCCEEDED without import~n")
            end;
        {error, Reason2} ->
            io:format("  ✗ Parse error: ~p~n", [Reason2])
    end,

    % Test 3: Create a test WITH import (should succeed)
    io:format("~nTest 3: Creating temporary file with import...~n"),
    WithImportFile = "/tmp/test_with_import.cure",
    WithImportCode =
        "# With Import Test\n"
        "module TestWithImport do\n"
        "  import Std.Show [show/1]\n"
        "  export [test/0]\n"
        "  \n"
        "  def test(): String =\n"
        "    show(42)\n"
        "end\n",
    file:write_file(WithImportFile, WithImportCode),
    io:format("  Type checking show usage WITH import (should succeed)...~n"),
    case cure_parser:parse_file(WithImportFile) of
        {ok, AST3} ->
            Result3 = cure_typechecker:check_program(AST3),
            case get_success(Result3) of
                true ->
                    io:format("  ✓ Type checking SUCCEEDED with import~n"),
                    io:format("~n~n==== ALL TESTS PASSED ====~n~n");
                false ->
                    io:format("  ✗ Type checking FAILED with import~n"),
                    print_errors(Result3),
                    io:format("~n~n==== SOME TESTS FAILED ====~n~n")
            end;
        {error, Reason3} ->
            io:format("  ✗ Parse error: ~p~n", [Reason3]),
            io:format("~n~n==== TESTS FAILED ====~n~n")
    end.

% Helper functions
get_success(Result) -> element(2, Result).
get_errors(Result) -> element(4, Result).
get_error_details(Error) -> element(4, Error).

check_for_unbound_variable([], _Name) ->
    false;
check_for_unbound_variable([Error | Rest], Name) ->
    Details = get_error_details(Error),
    case Details of
        {unbound_variable, Name, _Location} ->
            true;
        _ ->
            check_for_unbound_variable(Rest, Name)
    end.

print_errors(Result) ->
    Errors = get_errors(Result),
    lists:foreach(
        fun(E) ->
            Message = element(2, E),
            Details = element(4, E),
            io:format("    Error: ~s~n", [Message]),
            io:format("    Details: ~p~n", [Details])
        end,
        Errors
    ).
