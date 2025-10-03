%% Simple Performance Tests - Benchmark Cure compiler components
-module(performance_simple_test).

-export([run/0]).

-include("../src/parser/cure_ast.hrl").

%% Run all performance tests
run() ->
    io:format("Running Simple Performance tests...~n"),
    
    Tests = [
        fun test_lexer_performance_simple/0,
        fun test_type_checker_performance_simple/0,
        fun test_codegen_performance_simple/0,
        fun test_fsm_runtime_performance_simple/0
    ],
    
    Results = [run_performance_test(Test) || Test <- Tests],
    Passed = length([ok || ok <- Results]),
    Total = length(Results),
    
    io:format("Performance tests: ~w/~w passed~n", [Passed, Total]),
    
    case Passed of
        Total -> 
            io:format("All performance tests passed!~n"),
            ok;
        _ -> 
            io:format("Some performance tests failed~n"),
            error
    end.

%% Helper function to run performance tests with timing
run_performance_test(TestFun) ->
    try
        StartTime = erlang:monotonic_time(microsecond),
        TestFun(),
        EndTime = erlang:monotonic_time(microsecond),
        Duration = EndTime - StartTime,
        io:format("  Duration: ~w μs (~w ms)~n", [Duration, Duration div 1000]),
        ok
    catch
        Error:Reason:Stack ->
            io:format("❌ Performance test ~w failed: ~p:~p~n", [TestFun, Error, Reason]),
            io:format("Stack: ~p~n", [Stack]),
            error
    end.

%% Test 1: Lexer performance
test_lexer_performance_simple() ->
    io:format("✓ Testing lexer performance...~n"),
    
    % Generate some test data
    Numbers = [integer_to_list(N) ++ " " || N <- lists:seq(1, 1000)],
    Program = lists:flatten(Numbers),
    
    % Time the lexing process
    {ok, Tokens} = cure_lexer:scan(Program),
    
    % Verify we got tokens
    TokenCount = length(Tokens),
    true = TokenCount > 1000,
    
    io:format("  ✓ Lexed ~w tokens from performance test~n", [TokenCount]).

%% Test 2: Type checker performance  
test_type_checker_performance_simple() ->
    io:format("✓ Testing type checker performance...~n"),
    
    % Create type environment
    TypeEnv = cure_typechecker:builtin_env(),
    
    % Create multiple expressions to type check
    Expressions = [
        #literal_expr{value = N, location = undefined} 
        || N <- lists:seq(1, 100)
    ],
    
    % Type check all expressions
    Results = [cure_typechecker:infer_type(Expr, TypeEnv) || Expr <- Expressions],
    
    % Verify all succeeded
    SuccessCount = length([ok || {ok, _} <- Results]),
    100 = SuccessCount,
    
    io:format("  ✓ Type checked ~w expressions~n", [SuccessCount]).

%% Test 3: Code generation performance
test_codegen_performance_simple() ->
    io:format("✓ Testing code generation performance...~n"),
    
    % Create multiple expressions for code generation
    Expressions = [
        #literal_expr{value = N, location = undefined}
        || N <- lists:seq(1, 50)
    ],
    
    % Generate code for all expressions
    Results = [cure_codegen:compile_expression(Expr) || Expr <- Expressions],
    
    % Count total instructions
    TotalInstructions = lists:sum([
        length(Instructions) || {Instructions, _State} <- Results
    ]),
    
    true = TotalInstructions > 0,
    
    io:format("  ✓ Generated ~w BEAM instructions~n", [TotalInstructions]).

%% Test 4: FSM runtime performance
test_fsm_runtime_performance_simple() ->
    io:format("✓ Testing FSM runtime performance...~n"),
    
    % Register a simple FSM type
    FSMType = perf_test_fsm,
    States = [state_a, state_b],
    Transitions = [
        {state_a, event1, state_b, undefined, undefined},
        {state_b, event2, state_a, undefined, undefined}
    ],
    
    ok = cure_fsm_runtime:register_fsm_type(FSMType, States, state_a, Transitions),
    
    % Create multiple FSM instances
    FSMCount = 10,
    EventsPerFSM = 100,
    
    % Spawn FSMs
    FSMs = [cure_fsm_runtime:spawn_fsm(FSMType) || _ <- lists:seq(1, FSMCount)],
    
    % Send events to all FSMs
    [begin
        [cure_fsm_runtime:send_event(FSM, event1) || _ <- lists:seq(1, EventsPerFSM div 2)],
        [cure_fsm_runtime:send_event(FSM, event2) || _ <- lists:seq(1, EventsPerFSM div 2)]
     end || FSM <- FSMs],
    
    % Cleanup
    [cure_fsm_runtime:stop_fsm(FSM) || FSM <- FSMs],
    
    TotalEvents = FSMCount * EventsPerFSM,
    io:format("  ✓ Processed ~w events across ~w FSMs~n", [TotalEvents, FSMCount]).

%% Helper functions

%% Measure memory usage during operation
measure_memory_usage(Operation) ->
    erlang:garbage_collect(),
    {_, MemBefore} = erlang:process_info(self(), memory),
    
    Result = Operation(),
    
    erlang:garbage_collect(),
    {_, MemAfter} = erlang:process_info(self(), memory),
    
    {Result, MemAfter - MemBefore}.

%% Run operation multiple times and measure average
benchmark_operation(Operation, Times) ->
    Results = [begin
        StartTime = erlang:monotonic_time(microsecond),
        _Result = Operation(),
        EndTime = erlang:monotonic_time(microsecond),
        EndTime - StartTime
    end || _ <- lists:seq(1, Times)],
    
    TotalTime = lists:sum(Results),
    AvgTime = TotalTime div Times,
    MaxTime = lists:max(Results),
    MinTime = lists:min(Results),
    
    #{
        average => AvgTime,
        total => TotalTime,
        max => MaxTime,
        min => MinTime,
        samples => Times
    }.