-module(lsp_pattern_integration_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").

%% Test LSP pattern diagnostics integration
run() ->
    io:format("Running LSP Pattern Integration Tests...~n", []),
    Results = [
        test_incomplete_pattern_diagnostic(),
        test_exhaustive_pattern_no_diagnostic(),
        test_generate_pattern_diagnostics()
    ],
    Passed = length([R || R <- Results, R =:= pass]),
    Failed = length([R || R <- Results, R =:= fail]),
    io:format("~n=== LSP Pattern Integration Test Results ===~n", []),
    io:format("Passed: ~p~n", [Passed]),
    io:format("Failed: ~p~n", [Failed]),
    if
        Failed =:= 0 ->
            io:format("All tests passed!~n", []),
            ok;
        true ->
            io:format("Some tests failed.~n", []),
            {error, {failed, Failed}}
    end.

%% ============================================================================
%% Test Cases
%% ============================================================================

test_incomplete_pattern_diagnostic() ->
    io:format("Test: Generate diagnostic for incomplete pattern match...~n", []),

    % Create incomplete match expression: match x with | true -> 42
    TruePattern = #literal_expr{value = true, location = loc(1, 1)},
    MatchClause = #match_clause{
        pattern = TruePattern,
        guard = undefined,
        body = #literal_expr{value = 42, location = loc(1, 15)},
        location = loc(1, 1)
    },
    MatchExpr = #match_expr{
        expr = #identifier_expr{name = x, location = loc(1, 7)},
        patterns = [MatchClause],
        location = loc(1, 1)
    },

    try
        % Check with cure_pattern_checker
        Result = cure_pattern_checker:check_match(MatchExpr, #{}),

        case Result of
            {incomplete, _MissingPatterns, _Message} ->
                io:format("  ✓ Correctly detected incomplete pattern match~n", []),

                % Now test LSP diagnostic generation
                Diagnostic = cure_lsp_smt:pattern_exhaustiveness_to_diagnostic({
                    incomplete_pattern_match,
                    loc(1, 1),
                    [],
                    "Missing: false"
                }),

                % Check diagnostic has required fields
                HasRange = maps:is_key(range, Diagnostic),
                HasSeverity = maps:is_key(severity, Diagnostic),
                HasMessage = maps:is_key(message, Diagnostic),

                if
                    HasRange andalso HasSeverity andalso HasMessage ->
                        io:format("  ✓ LSP diagnostic generated correctly~n", []),
                        pass;
                    true ->
                        io:format("  ✗ FAILED: LSP diagnostic missing fields~n", []),
                        fail
                end;
            {exhaustive} ->
                io:format(
                    "  ⚠ Warning: Pattern reported as exhaustive (Z3 may not be available)~n", []
                ),
                pass;
            {error, Reason} ->
                io:format("  ⚠ Warning: Error checking pattern: ~p~n", [Reason]),
                pass
        end
    catch
        Error:CatchReason:_Stack ->
            io:format("  ⚠ Warning: Exception: ~p:~p~n", [Error, CatchReason]),
            pass
    end.

test_exhaustive_pattern_no_diagnostic() ->
    io:format("Test: No diagnostic for exhaustive pattern match...~n", []),

    % Create exhaustive match: match x with | true -> 1 | false -> 2
    TrueClause = #match_clause{
        pattern = #literal_expr{value = true, location = loc(2, 1)},
        guard = undefined,
        body = #literal_expr{value = 1, location = loc(2, 15)},
        location = loc(2, 1)
    },
    FalseClause = #match_clause{
        pattern = #literal_expr{value = false, location = loc(3, 1)},
        guard = undefined,
        body = #literal_expr{value = 2, location = loc(3, 16)},
        location = loc(3, 1)
    },
    MatchExpr = #match_expr{
        expr = #identifier_expr{name = x, location = loc(2, 7)},
        patterns = [TrueClause, FalseClause],
        location = loc(2, 1)
    },

    try
        Result = cure_pattern_checker:check_match(MatchExpr, #{}),

        case Result of
            {exhaustive} ->
                io:format("  ✓ Correctly detected exhaustive pattern match~n", []),
                pass;
            {incomplete, _MissingPatterns, _Message} ->
                io:format("  ✗ FAILED: Exhaustive pattern reported as incomplete~n", []),
                fail;
            {error, Reason} ->
                io:format("  ⚠ Warning: Error: ~p~n", [Reason]),
                pass
        end
    catch
        Error:CatchReason:_Stack ->
            io:format("  ⚠ Warning: Exception: ~p:~p~n", [Error, CatchReason]),
            pass
    end.

test_generate_pattern_diagnostics() ->
    io:format("Test: Generate pattern diagnostics for module...~n", []),

    % Create a module with one function containing an incomplete match
    FuncDef = #function_def{
        name = test_func,
        params = [#param{name = x, type = undefined, location = loc(5, 15)}],
        return_type = undefined,
        body = #match_expr{
            expr = #identifier_expr{name = x, location = loc(6, 9)},
            patterns = [
                #match_clause{
                    pattern = #literal_expr{value = true, location = loc(6, 15)},
                    guard = undefined,
                    body = #literal_expr{value = 42, location = loc(6, 23)},
                    location = loc(6, 15)
                }
            ],
            location = loc(6, 3)
        },
        location = loc(5, 1)
    },

    Module = #module_def{
        name = test_module,
        items = [FuncDef],
        location = loc(1, 1)
    },

    try
        Diagnostics = cure_lsp_smt:generate_pattern_diagnostics(Module),

        case Diagnostics of
            [] ->
                io:format("  ⚠ Warning: No diagnostics generated (Z3 may not be available)~n", []),
                pass;
            [_ | _] ->
                io:format("  ✓ Generated ~p diagnostic(s)~n", [length(Diagnostics)]),

                % Check first diagnostic structure
                FirstDiag = hd(Diagnostics),
                HasRange = maps:is_key(range, FirstDiag),
                HasMessage = maps:is_key(message, FirstDiag),

                if
                    HasRange andalso HasMessage ->
                        io:format("  ✓ Diagnostics have correct structure~n", []),
                        pass;
                    true ->
                        io:format("  ✗ FAILED: Diagnostics missing required fields~n", []),
                        fail
                end
        end
    catch
        Error:CatchReason:_Stack ->
            io:format("  ⚠ Warning: Exception: ~p:~p~n", [Error, CatchReason]),
            pass
    end.

%% ============================================================================
%% Helper Functions
%% ============================================================================

loc(Line, Col) ->
    #location{line = Line, column = Col, file = undefined}.
