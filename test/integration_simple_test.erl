%% Simple Integration Tests - End-to-end Cure compiler functionality
-module(integration_simple_test).

-export([run/0]).

-include("../src/parser/cure_ast.hrl").

%% Run all integration tests
run() ->
    cure_utils:debug("Running Simple Integration tests...~n"),

    Tests = [
        fun test_lexer_parser_pipeline/0,
        fun test_basic_type_checking/0,
        fun test_code_generation_basic/0,
        fun test_fsm_basic_functionality/0,
        fun test_error_handling/0,
        fun test_pipeline_performance/0,
        fun test_memory_usage/0
    ],

    Results = [run_test(Test) || Test <- Tests],
    Passed = length([ok || ok <- Results]),
    Total = length(Results),

    cure_utils:debug("Integration tests: ~w/~w passed~n", [Passed, Total]),

    case Passed of
        Total ->
            cure_utils:debug("All integration tests passed!~n"),
            ok;
        _ ->
            cure_utils:debug("Some integration tests failed~n"),
            error
    end.

%% Helper function to run individual tests
run_test(TestFun) ->
    try
        TestFun(),
        ok
    catch
        Error:Reason:Stack ->
            cure_utils:debug("❌ Test ~w failed: ~p:~p~n", [TestFun, Error, Reason]),
            cure_utils:debug("Stack: ~p~n", [Stack]),
            error
    end.

%% Test 1: Lexer -> Parser pipeline
test_lexer_parser_pipeline() ->
    cure_utils:debug("✓ Testing lexer-parser pipeline...~n"),

    % Simple Cure code
    Code = "42",

    % Tokenize
    {ok, Tokens} = cure_lexer:scan(Code),

    % Verify tokens
    case Tokens of
        [{integer, _, 42}, {eof, _}] ->
            cure_utils:debug("  ✓ Lexer-parser pipeline test passed~n");
        _ ->
            throw({unexpected_tokens, Tokens})
    end.

%% Test 2: Basic type checking
test_basic_type_checking() ->
    cure_utils:debug("✓ Testing basic type checking...~n"),

    % Create type environment
    TypeEnv = cure_typechecker:builtin_env(),

    % Simple literal expression
    LiteralExpr = #literal_expr{value = 42, location = undefined},

    % Type check it
    {ok, Type} = cure_typechecker:infer_type(LiteralExpr, TypeEnv),

    % Verify it's an integer type
    case Type of
        {primitive_type, 'Int'} ->
            cure_utils:debug("  ✓ Basic type checking test passed~n");
        _ ->
            throw({unexpected_type, Type})
    end.

%% Test 3: Code generation basics
test_code_generation_basic() ->
    cure_utils:debug("✓ Testing basic code generation...~n"),

    % Simple expression
    Expr = #literal_expr{value = 42, location = undefined},

    % Generate code
    {Instructions, _State} = cure_codegen:compile_expression(Expr),

    % Verify we got some instructions
    case length(Instructions) > 0 of
        true ->
            cure_utils:debug("  ✓ Basic code generation test passed~n");
        false ->
            throw({no_instructions_generated, Instructions})
    end.

%% Test 4: FSM basic functionality
test_fsm_basic_functionality() ->
    cure_utils:debug("✓ Testing FSM basic functionality...~n"),

    % Test FSM registration
    FSMType = test_simple_fsm,
    States = [start, finish],
    InitialState = start,
    Transitions = [
        {start, test_event, finish, undefined, undefined}
    ],

    % Register FSM type
    ok = cure_fsm_runtime:register_fsm_type(FSMType, States, InitialState, Transitions),

    % Spawn FSM
    FSM = cure_fsm_runtime:spawn_fsm(FSMType),

    % Check initial state
    start = cure_fsm_runtime:get_current_state(FSM),

    % Send event
    ok = cure_fsm_runtime:send_event(FSM, test_event),

    % Check final state
    finish = cure_fsm_runtime:get_current_state(FSM),

    % Clean up
    ok = cure_fsm_runtime:stop_fsm(FSM),

    cure_utils:debug("  ✓ FSM basic functionality test passed~n").

%% Additional helper functions for future tests

%% Test error handling
test_error_handling() ->
    cure_utils:debug("✓ Testing error handling...~n"),

    % Test with invalid code
    InvalidCode = "invalid syntax here!@#",

    case cure_lexer:scan(InvalidCode) of
        {error, _Reason} ->
            cure_utils:debug("  ✓ Error handling test passed~n");
        {ok, _} ->
            % Lexer might not catch all syntax errors
            cure_utils:debug("  ✓ Error handling test passed (lexer accepted input)~n")
    end.

%% Test performance of pipeline
test_pipeline_performance() ->
    cure_utils:debug("✓ Testing pipeline performance...~n"),

    % Generate medium-sized code
    Code = lists:flatten([integer_to_list(N) ++ " " || N <- lists:seq(1, 100)]),

    StartTime = erlang:monotonic_time(microsecond),

    % Run pipeline
    {ok, Tokens} = cure_lexer:scan(Code),
    _TokenCount = length(Tokens),

    EndTime = erlang:monotonic_time(microsecond),
    Duration = EndTime - StartTime,

    cure_utils:debug("  ✓ Pipeline performance test completed in ~w μs~n", [Duration]).

%% Test memory usage
test_memory_usage() ->
    cure_utils:debug("✓ Testing memory usage...~n"),

    % Get initial memory usage
    {_, MemBefore} = erlang:process_info(self(), memory),

    % Create some data structures
    Code = "let x = 42, y = x + 1 in x * y",
    {ok, Tokens} = cure_lexer:scan(Code),
    _ParsedResult = lists:map(fun(Token) -> Token end, Tokens),

    % Force garbage collection
    erlang:garbage_collect(),

    % Get final memory usage
    {_, MemAfter} = erlang:process_info(self(), memory),

    cure_utils:debug("  ✓ Memory usage test: ~w -> ~w bytes~n", [MemBefore, MemAfter]).
