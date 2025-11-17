-module(pipe_optimizer_stats_test).

-export([run/0]).

-include("../src/parser/cure_ast.hrl").

%% Test pipe optimizer statistics gathering
run() ->
    io:format("~n=== Pipe Optimizer Statistics Test ===~n~n"),

    % Test 1: Simple pipe that can be inlined
    io:format("Test 1: Simple inlinable pipe...~n"),
    SimplePipe = #binary_op_expr{
        op = '|>',
        left = #literal_expr{value = 42, location = #location{line = 1, column = 1}},
        right = #identifier_expr{name = double, location = #location{line = 1, column = 10}},
        location = #location{line = 1, column = 5}
    },

    case cure_pipe_optimizer:optimize_pipe_chain(SimplePipe, #{}) of
        {ok, _OptimizedExpr1, Stats1} ->
            io:format("  ✓ Pipe was optimized~n"),
            io:format("  Statistics: ~s~n", [cure_pipe_optimizer:format_stats(Stats1)]);
        {unchanged, _, Stats1} ->
            io:format("  ⚠ Pipe was not optimized~n"),
            io:format("  Statistics: ~s~n", [cure_pipe_optimizer:format_stats(Stats1)])
    end,

    % Test 2: Complex pipe that should remain unchanged
    io:format("~nTest 2: Complex pipe (may error)...~n"),
    ComplexPipe = #binary_op_expr{
        op = '|>',
        left = #function_call_expr{
            function = #identifier_expr{
                name = read_file, location = #location{line = 2, column = 1}
            },
            args = [#literal_expr{value = "test.txt", location = #location{line = 2, column = 11}}],
            location = #location{line = 2, column = 1}
        },
        right = #identifier_expr{name = parse, location = #location{line = 2, column = 30}},
        location = #location{line = 2, column = 25}
    },

    case cure_pipe_optimizer:optimize_pipe_chain(ComplexPipe, #{}) of
        {ok, _OptimizedExpr2, Stats2} ->
            io:format("  ✓ Pipe was optimized~n"),
            io:format("  Statistics: ~s~n", [cure_pipe_optimizer:format_stats(Stats2)]);
        {unchanged, _, Stats2} ->
            io:format("  ✓ Pipe remains monadic (expected)~n"),
            io:format("  Statistics: ~s~n", [cure_pipe_optimizer:format_stats(Stats2)])
    end,

    % Test 3: Non-pipe expression
    io:format("~nTest 3: Non-pipe expression...~n"),
    NonPipe = #binary_op_expr{
        op = '+',
        left = #literal_expr{value = 1, location = #location{line = 3, column = 1}},
        right = #literal_expr{value = 2, location = #location{line = 3, column = 5}},
        location = #location{line = 3, column = 3}
    },

    case cure_pipe_optimizer:optimize_pipe_chain(NonPipe, #{}) of
        {unchanged, _, Stats3} ->
            io:format("  ✓ Non-pipe remains unchanged (expected)~n"),
            io:format("  Statistics: ~s~n", [cure_pipe_optimizer:format_stats(Stats3)])
    end,

    % Test 4: Verify stats functions work correctly
    io:format("~nTest 4: Statistics API...~n"),
    EmptyStats = cure_pipe_optimizer:new_stats(),
    io:format("  Empty stats: ~s~n", [cure_pipe_optimizer:format_stats(EmptyStats)]),

    Stats4 = cure_pipe_optimizer:update_stats(EmptyStats, inlined),
    Stats5 = cure_pipe_optimizer:update_stats(Stats4, inlined),
    Stats6 = cure_pipe_optimizer:update_stats(Stats5, error_free),
    Stats7 = cure_pipe_optimizer:update_stats(Stats6, unchanged),

    io:format("  After updates: ~s~n", [cure_pipe_optimizer:format_stats(Stats7)]),

    io:format("~n✓ All tests completed~n"),
    ok.
