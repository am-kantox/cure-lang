%% Performance Tests - Benchmark Cure compiler components
-module(performance_test).

-export([run/0]).

-include("../src/parser/cure_ast.hrl").
-include("../src/types/cure_type_optimizer.hrl").

%% Run all performance tests
run() ->
    io:format("Running Performance tests...~n"),

    Tests = [
        fun test_lexer_performance/0,
        fun test_parser_performance/0,
        fun test_type_checker_performance/0,
        fun test_codegen_performance/0,
        fun test_fsm_runtime_performance/0,
        fun test_large_program_compilation/0
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

%% Test 1: Lexer performance with large input
test_lexer_performance() ->
    io:format("✓ Testing lexer performance...~n"),

    % Generate a large Cure program

    % 1000 functions
    LargeProgram = generate_large_program(1000),

    % Time the lexing process
    {ok, Tokens} = cure_lexer:scan(LargeProgram),

    % Verify we got a reasonable number of tokens
    TokenCount = length(Tokens),
    % Should have many tokens
    true = TokenCount > 5000,

    io:format("  ✓ Lexed ~w tokens from large program~n", [TokenCount]).

%% Test 2: Parser performance
test_parser_performance() ->
    io:format("✓ Testing parser performance...~n"),

    % Generate medium-sized program

    % 100 functions
    Program = generate_medium_program(100),

    % Tokenize first
    {ok, Tokens} = cure_lexer:scan(Program),

    % Time the parsing process
    {ok, AST} = cure_parser:parse(Tokens),

    % Verify AST structure
    case AST of
        #module_def{items = Items} ->
            FunctionCount = length(Items),
            true = FunctionCount >= 100,
            ok;
        _ ->
            throw({unexpected_ast_structure, AST})
    end,

    io:format("  ✓ Parsed program with ~w functions~n", [length(AST#module_def.items)]).

%% Test 3: Type checker performance
test_type_checker_performance() ->
    io:format("✓ Testing type checker performance...~n"),

    % Create program with complex type relationships
    Program = generate_type_heavy_program(),

    {ok, Tokens} = cure_lexer:scan(Program),
    {ok, AST} = cure_parser:parse(Tokens),

    % Time type checking
    TypeEnv = cure_typechecker:builtin_env(),
    {ok, _TypedAST} = cure_typechecker:check_module(AST, TypeEnv),

    io:format("  ✓ Type checked complex program successfully~n").

%% Test 4: Code generation performance
test_codegen_performance() ->
    io:format("✓ Testing code generation performance...~n"),

    % Simple program for code generation
    Program = generate_codegen_program(),

    {ok, Tokens} = cure_lexer:scan(Program),
    {ok, AST} = cure_parser:parse(Tokens),

    % Time code generation
    {ok, Instructions} = cure_codegen:compile_module(AST, #{}),

    % Verify we got instructions
    InstructionCount = length(Instructions),
    true = InstructionCount > 0,

    io:format("  ✓ Generated ~w BEAM instructions~n", [InstructionCount]).

%% Test 5: FSM runtime performance
test_fsm_runtime_performance() ->
    io:format("✓ Testing FSM runtime performance...~n"),

    % Register a simple FSM type
    FSMType = test_counter_fsm,
    States = [zero, one, two],
    Transitions = [
        {zero, increment, one, undefined, undefined},
        {one, increment, two, undefined, undefined},
        {two, reset, zero, undefined, undefined}
    ],

    ok = cure_fsm_runtime:register_fsm_type(FSMType, States, zero, Transitions),

    % Create many FSM instances and send many events
    FSMCount = 100,
    EventCount = 1000,

    % Spawn FSMs
    FSMs = [cure_fsm_runtime:spawn_fsm(FSMType) || _ <- lists:seq(1, FSMCount)],

    % Send events to all FSMs
    [
        begin
            [cure_fsm_runtime:send_event(FSM, increment) || _ <- lists:seq(1, EventCount div 100)]
        end
     || FSM <- FSMs
    ],

    % Cleanup
    [cure_fsm_runtime:stop_fsm(FSM) || FSM <- FSMs],

    io:format("  ✓ Processed ~w events across ~w FSMs~n", [EventCount, FSMCount]).

%% Test 6: Large program compilation (end-to-end)
test_large_program_compilation() ->
    io:format("✓ Testing large program compilation...~n"),

    % Generate a large, complex program
    LargeProgram = generate_comprehensive_program(),

    % Full compilation pipeline
    {ok, Tokens} = cure_lexer:scan(LargeProgram),
    {ok, AST} = cure_parser:parse(Tokens),

    TypeEnv = cure_typechecker:builtin_env(),
    {ok, TypedAST} = cure_typechecker:check_module(AST, TypeEnv),

    {ok, Instructions} = cure_codegen:compile_module(TypedAST, #{}),

    % Verify comprehensive compilation
    InstructionCount = length(Instructions),
    true = InstructionCount > 100,

    io:format("  ✓ Compiled large program to ~w instructions~n", [InstructionCount]).

%% Helper functions to generate test programs

%% Generate a large program with many functions
generate_large_program(FunctionCount) ->
    ModuleHeader =
        "module LargeTest do\n"
        "  export [" ++ generate_exports(FunctionCount) ++ "]\n\n",

    Functions = [generate_function(N) || N <- lists:seq(1, FunctionCount)],

    ModuleHeader ++ lists:flatten(Functions) ++ "end\n".

%% Generate exports list
generate_exports(Count) ->
    Exports = [io_lib:format("func~w/1", [N]) || N <- lists:seq(1, Count)],
    string_join(Exports, ", ").

%% Generate a single function
generate_function(N) ->
    io_lib:format(
        "  def func~w(x: Int): Int =~n"
        "    if x > 0 then~n"
        "      x + func~w(x - 1)~n"
        "    else~n"
        "      ~w~n"
        "    end~n~n",
        [N, max(1, N - 1), N]
    ).

%% Generate medium-sized program
generate_medium_program(FunctionCount) ->
    ModuleHeader =
        "module MediumTest do\n"
        "  export [main/0]\n\n",

    Functions = [generate_recursive_function(N) || N <- lists:seq(1, FunctionCount)],

    MainFunction =
        "  def main(): Int =\n"
        "    let results = [" ++
            string:join(
                [io_lib:format("func~w(~w)", [N, N]) || N <- lists:seq(1, min(10, FunctionCount))],
                ", "
            ) ++
            "]\n"
            "    sum(results)\n\n",

    ModuleHeader ++ lists:flatten(Functions) ++ MainFunction ++ "end\n".

%% Generate recursive function
generate_recursive_function(N) ->
    io_lib:format(
        "  def func~w(n: Nat): Nat =~n"
        "    match n do~n"
        "      0 -> ~w~n"
        "      n -> n + func~w(n - 1)~n"
        "    end~n~n",
        [N, N, N]
    ).

%% Generate type-heavy program for type checker testing
generate_type_heavy_program() ->
    "module TypeHeavy do\n"
    "  export [main/0]\n\n"
    % Polymorphic functions
    "  def identity(x: T) -> T = x\n\n"
    "  def compose(f: B -> C, g: A -> B, x: A): C = f(g(x))\n\n"
    % Dependent types
    "  def safe_head(list: List(T, n)) -> T when n > 0 =\n"
    "    match list do\n"
    "      [x|_] -> x\n"
    "    end\n\n"
    "  def safe_tail(list: List(T, n)) -> List(T, n-1) when n > 0 =\n"
    "    match list do\n"
    "      [_|xs] -> xs\n"
    "    end\n\n"
    % Higher-order functions
    "  def map(f: A -> B, list: List(A)): List(B) =\n"
    "    match list do\n"
    "      [] -> []\n"
    "      [x|xs] -> [f(x) | map(f, xs)]\n"
    "    end\n\n"
    "  def fold(f: A -> B -> A, acc: A, list: List(B)): A =\n"
    "    match list do\n"
    "      [] -> acc\n"
    "      [x|xs] -> fold(f, f(acc, x), xs)\n"
    "    end\n\n"
    % Complex type combinations
    "  def complex_func(x: Int, y: List(String), z: Maybe(Bool)): Result(Int, String) =\n"
    "    match z do\n"
    "      Just(true) -> Ok(x + length(y))\n"
    "      Just(false) -> Error(\"false condition\")\n"
    "      Nothing -> Error(\"no condition\")\n"
    "    end\n\n"
    "  def main(): Int = 42\n"
    "end\n".

%% Generate program for code generation testing
generate_codegen_program() ->
    "module CodegenTest do\n"
    "  export [main/0]\n\n"
    % Arithmetic operations
    "  def arithmetic(x: Int, y: Int): Int =\n"
    "    let a = x + y\n"
    "    let b = x * y  \n"
    "    let c = x - y\n"
    "    let d = x / y\n"
    "    a + b + c + d\n\n"
    % Function calls
    "  def factorial(n: Nat): Nat =\n"
    "    if n <= 1 then\n"
    "      1\n"
    "    else\n"
    "      n * factorial(n - 1)\n"
    "    end\n\n"
    % Pattern matching
    "  def list_length(list: List(T)): Nat =\n"
    "    match list do\n"
    "      [] -> 0\n"
    "      [_|xs] -> 1 + list_length(xs)\n"
    "    end\n\n"
    % Let expressions
    "  def complex_let(): Int =\n"
    "    let x = 10\n"
    "    let y = x * 2\n"
    "    let z = arithmetic(x, y)\n"
    "    let w = factorial(5)\n"
    "    z + w\n\n"
    "  def main(): Int = complex_let()\n"
    "end\n".

%% Generate comprehensive program combining multiple features
generate_comprehensive_program() ->
    "module Comprehensive do\n"
    "  export [main/0]\n\n"
    % Include FSM
    "  fsm StateMachine do\n"
    "    states: [Init, Processing, Complete, Error]\n"
    "    initial: Init\n"
    "    \n"
    "    state Init do\n"
    "      event(:start) -> Processing\n"
    "      event(:error) -> Error\n"
    "    end\n"
    "    \n"
    "    state Processing do\n"
    "      event(:complete) -> Complete\n"
    "      event(:error) -> Error\n"
    "    end\n"
    "    \n"
    "    state Complete do\n"
    "      event(:reset) -> Init\n"
    "    end\n"
    "    \n"
    "    state Error do\n"
    "      event(:reset) -> Init\n"
    "    end\n"
    "  end\n\n"
    % Complex functions with various features
    "  def process_data(data: List(Int)): Result(Int, String) =\n"
    "    let machine = fsm_spawn(StateMachine)\n"
    "    fsm_send(machine, :start)\n"
    "    \n"
    "    let result = match data do\n"
    "      [] -> Error(\"empty data\")\n"
    "      [x|xs] when x > 0 -> \n"
    "        let processed = map(square, data)\n"
    "        let sum = fold(add, 0, processed)\n"
    "        fsm_send(machine, :complete)\n"
    "        Ok(sum)\n"
    "      _ ->\n"
    "        fsm_send(machine, :error)\n"
    "        Error(\"invalid data\")\n"
    "    end\n"
    "    \n"
    "    fsm_stop(machine)\n"
    "    result\n\n"
    "  def square(x: Int): Int = x * x\n\n"
    "  def add(x: Int, y: Int): Int = x + y\n\n"
    "  def map(f: A -> B, list: List(A)): List(B) =\n"
    "    match list do\n"
    "      [] -> []\n"
    "      [x|xs] -> [f(x) | map(f, xs)]\n"
    "    end\n\n"
    "  def fold(f: A -> B -> A, acc: A, list: List(B)): A =\n"
    "    match list do\n"
    "      [] -> acc\n"
    "      [x|xs] -> fold(f, f(acc, x), xs)\n"
    "    end\n\n"
    "  def main(): Int =\n"
    "    let test_data = [1, 2, 3, 4, 5]\n"
    "    match process_data(test_data) do\n"
    "      Ok(result) -> result\n"
    "      Error(_) -> -1\n"
    "    end\n"
    "end\n".

%% Utility function for string joining (if not available)
string_join([], _Sep) -> "";
string_join([H | T], Sep) -> lists:foldl(fun(E, Acc) -> Acc ++ Sep ++ E end, H, T).
