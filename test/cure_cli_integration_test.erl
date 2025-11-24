-module(cure_cli_integration_test).

-export([run/0, test_emit_ast/0, test_emit_typed_ast/0, test_check_only/0, test_smt_options/0]).

%% Simple integration tests for CLI options
%% These are manual tests to verify CLI functionality

run() ->
    io:format("Running CLI integration tests...~n"),

    % Test 1: --emit-ast
    test_emit_ast(),

    % Test 2: --emit-typed-ast
    test_emit_typed_ast(),

    % Test 3: --check
    test_check_only(),

    % Test 4: SMT options
    test_smt_options(),

    io:format("~nAll CLI integration tests completed.~n"),
    ok.

test_emit_ast() ->
    io:format("~nTest 1: --emit-ast option~n"),
    io:format("  Command: ./cure test/cli_test_minimal.cure --emit-ast --no-type-check~n"),
    Output = os:cmd(
        "cd /opt/Proyectos/Ammotion/cure && ./cure test/cli_test_minimal.cure --emit-ast --no-type-check 2>&1"
    ),
    case string:str(Output, "=== Abstract Syntax Tree ===") of
        0 ->
            io:format("  FAILED: AST not emitted~n"),
            error;
        _ ->
            io:format("  PASSED: AST emitted successfully~n"),
            ok
    end.

test_emit_typed_ast() ->
    io:format("~nTest 2: --emit-typed-ast option~n"),
    io:format("  Command: ./cure test/cli_test_minimal.cure --emit-typed-ast --check~n"),
    Output = os:cmd(
        "cd /opt/Proyectos/Ammotion/cure && ./cure test/cli_test_minimal.cure --emit-typed-ast --check 2>&1"
    ),
    case string:str(Output, "=== Typed Abstract Syntax Tree ===") of
        0 ->
            io:format("  FAILED: Typed AST not emitted~n"),
            error;
        _ ->
            io:format("  PASSED: Typed AST emitted successfully~n"),
            ok
    end.

test_check_only() ->
    io:format("~nTest 3: --check option~n"),
    io:format("  Command: ./cure test/cli_test_minimal.cure --check~n"),
    Output = os:cmd(
        "cd /opt/Proyectos/Ammotion/cure && ./cure test/cli_test_minimal.cure --check 2>&1"
    ),
    case string:str(Output, "Type checking completed successfully") of
        0 ->
            io:format("  FAILED: Check-only mode did not complete~n"),
            error;
        _ ->
            % Verify no BEAM file was created
            BeamFile = "_build/ebin/CliTestMinimal.beam",
            case filelib:is_regular(BeamFile) of
                true ->
                    io:format("  WARNING: BEAM file created in check-only mode~n"),
                    ok;
                false ->
                    io:format("  PASSED: Check-only completed, no BEAM generated~n"),
                    ok
            end
    end.

test_smt_options() ->
    io:format("~nTest 4: SMT options~n"),

    % Test --no-smt
    io:format("  Subtest 4a: --no-smt~n"),
    io:format("    Command: ./cure test/cli_test_minimal.cure --check --no-smt~n"),
    Output1 = os:cmd(
        "cd /opt/Proyectos/Ammotion/cure && ./cure test/cli_test_minimal.cure --check --no-smt 2>&1"
    ),
    case string:str(Output1, "Type checking completed successfully") of
        0 ->
            io:format("    FAILED: --no-smt did not complete~n");
        _ ->
            io:format("    PASSED: --no-smt works~n")
    end,

    % Test --smt-solver
    io:format("  Subtest 4b: --smt-solver z3~n"),
    io:format("    Command: ./cure test/cli_test_minimal.cure --check --smt-solver z3~n"),
    Output2 = os:cmd(
        "cd /opt/Proyectos/Ammotion/cure && ./cure test/cli_test_minimal.cure --check --smt-solver z3 2>&1"
    ),
    case string:str(Output2, "Type checking completed successfully") of
        0 ->
            io:format("    FAILED: --smt-solver z3 did not complete~n");
        _ ->
            io:format("    PASSED: --smt-solver z3 works~n")
    end,

    % Test --smt-timeout
    io:format("  Subtest 4c: --smt-timeout 10000~n"),
    io:format("    Command: ./cure test/cli_test_minimal.cure --check --smt-timeout 10000~n"),
    Output3 = os:cmd(
        "cd /opt/Proyectos/Ammotion/cure && ./cure test/cli_test_minimal.cure --check --smt-timeout 10000 2>&1"
    ),
    case string:str(Output3, "Type checking completed successfully") of
        0 ->
            io:format("    FAILED: --smt-timeout 10000 did not complete~n");
        _ ->
            io:format("    PASSED: --smt-timeout 10000 works~n")
    end,

    ok.
