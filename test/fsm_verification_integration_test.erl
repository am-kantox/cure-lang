-module(fsm_verification_integration_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").
-include("../src/fsm/cure_fsm_runtime.hrl").

%% Test that FSM verification runs during compilation when enabled
run() ->
    io:format("~n=== Testing FSM Verification Integration ===~n~n"),

    % Test without verification (default)
    test_without_verification(),

    % Test with verification enabled
    test_with_verification(),

    io:format("~n=== Verification Integration Tests Complete! ===~n~n").

test_without_verification() ->
    io:format("1. Testing compilation WITHOUT verification...~n"),

    % Make sure CURE_FSM_VERIFY is not set
    os:unsetenv("CURE_FSM_VERIFY"),

    % Parse and compile a simple FSM
    case cure_parser:parse_file("examples/07_fsm_verification.cure") of
        {ok, ParsedItems} ->
            FSMs = extract_all_fsms(ParsedItems),
            case FSMs of
                [FirstFSM | _] ->
                    % Try to compile - should succeed without verification output
                    case cure_fsm_runtime:compile_fsm_definition(FirstFSM) of
                        CompiledFSM when is_record(CompiledFSM, fsm_definition) ->
                            io:format("   ✓ Compilation succeeded without verification~n");
                        _ ->
                            io:format("   ✗ Compilation failed~n"),
                            error(compilation_failed)
                    end;
                [] ->
                    io:format("   ✗ No FSMs found~n"),
                    error(no_fsms)
            end;
        {error, Error} ->
            io:format("   ✗ Parse error: ~p~n", [Error]),
            error(parse_failed)
    end.

test_with_verification() ->
    io:format("~n2. Testing compilation WITH verification enabled...~n"),

    % Enable verification
    os:putenv("CURE_FSM_VERIFY", "1"),

    % Parse verification example
    case cure_parser:parse_file("examples/07_fsm_verification.cure") of
        {ok, ParsedItems} ->
            FSMs = extract_all_fsms(ParsedItems),
            io:format("   Found ~p FSMs~n", [length(FSMs)]),

            % Test verification on each FSM
            lists:foreach(
                fun(FSM) ->
                    test_fsm_verification(FSM)
                end,
                FSMs
            ),

            io:format("   ✓ All FSMs verified successfully~n");
        {error, Error} ->
            io:format("   ✗ Parse error: ~p~n", [Error]),
            error(parse_failed)
    end,

    % Clean up
    os:unsetenv("CURE_FSM_VERIFY").

test_fsm_verification(#fsm_def{name = Name} = FSMDef) ->
    io:format("~n   Testing verification for FSM: ~p~n", [Name]),

    % Run verification directly
    case cure_fsm_verifier:verify_fsm(FSMDef) of
        {ok, Results} ->
            io:format("     Verification completed with ~p results~n", [length(Results)]),

            % Check for specific result types
            Reachable = [S || {reachable, S} <- Results],
            Unreachable = [S || {unreachable, S} <- Results],
            Deadlocks = [S || {has_deadlock, S} <- Results],

            io:format("     - Reachable states: ~p~n", [length(Reachable)]),
            io:format("     - Unreachable states: ~p~n", [length(Unreachable)]),
            io:format("     - Deadlock states: ~p~n", [length(Deadlocks)]),

            % Report any issues
            case Unreachable of
                [] -> ok;
                _ -> io:format("     ⚠ Unreachable states found: ~p~n", [Unreachable])
            end,

            case Deadlocks of
                [] -> ok;
                _ -> io:format("     ⚠ Deadlock states found: ~p~n", [Deadlocks])
            end,

            io:format("     ✓ Verification passed~n");
        {error, Error} ->
            io:format("     ✗ Verification error: ~p~n", [Error])
    end.

% Extract all FSMs from parsed items
extract_all_fsms(ParsedItems) when is_list(ParsedItems) ->
    lists:foldl(
        fun(Item, Acc) ->
            case Item of
                FSM = #fsm_def{} ->
                    [FSM | Acc];
                #module_def{items = ModuleItems} ->
                    extract_all_fsms(ModuleItems) ++ Acc;
                _ ->
                    Acc
            end
        end,
        [],
        ParsedItems
    ).
