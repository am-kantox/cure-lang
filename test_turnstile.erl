-module(test_turnstile).
-export([test/0]).

-record(typecheck_result, {success, type, errors, warnings}).
-record(typecheck_error, {message, location, details}).
-record(typecheck_warning, {message, location, details}).

test() ->
    io:format("=== Testing turnstile.cure ===~n"),
    case cure_parser:parse_file("examples/turnstile.cure") of
        {ok, AST} ->
            io:format("Parsed successfully~n"),
            Result = cure_typechecker:check_program(AST),
            io:format("Type check success: ~p~n", [Result#typecheck_result.success]),
            case Result#typecheck_result.errors of
                [] ->
                    io:format("No errors!~n");
                Errors ->
                    io:format("~nErrors found:~n"),
                    lists:foreach(
                        fun(Error) ->
                            io:format("  - ~s~n", [Error#typecheck_error.message]),
                            io:format("    Details: ~p~n", [Error#typecheck_error.details])
                        end,
                        Errors
                    )
            end,
            case Result#typecheck_result.warnings of
                [] ->
                    ok;
                Warnings ->
                    io:format("~nWarnings found:~n"),
                    lists:foreach(
                        fun(Warning) ->
                            io:format("  - ~s~n", [Warning#typecheck_warning.message])
                        end,
                        Warnings
                    )
            end;
        {error, Reason} ->
            io:format("Parse error: ~p~n", [Reason])
    end.
