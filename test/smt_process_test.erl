-module(smt_process_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").

run() ->
    io:format("~n=== SMT Solver Process Management Tests ===~n~n"),

    Tests = [
        fun test_z3_startup/0,
        fun test_simple_query/0,
        fun test_satisfiable_constraint/0,
        fun test_unsatisfiable_constraint/0,
        fun test_reset/0,
        fun test_statistics/0,
        fun test_translator_integration/0
    ],

    Results = lists:map(fun run_test/1, Tests),

    Passed = length([R || R <- Results, R =:= ok]),
    Failed = length(Results) - Passed,

    io:format("~n=== Results ===~n"),
    io:format("Passed: ~p~n", [Passed]),
    io:format("Failed: ~p~n", [Failed]),
    io:format("Total:  ~p~n", [length(Results)]),

    case Failed of
        0 -> io:format("~n✅ All tests passed!~n~n");
        _ -> io:format("~n❌ Some tests failed!~n~n")
    end,

    ok.

run_test(TestFun) ->
    try
        TestFun(),
        ok
    catch
        Class:Reason:Stack ->
            io:format("  ❌ FAILED: ~p:~p~n", [Class, Reason]),
            io:format("     Stack: ~p~n", [Stack]),
            error
    end.

test_z3_startup() ->
    io:format("Testing Z3 startup... "),
    {ok, Pid} = cure_smt_process:start_solver(z3, 5000),
    cure_smt_process:stop_solver(Pid),
    io:format("✅~n"),
    ok.

test_simple_query() ->
    io:format("Testing simple query... "),
    {ok, Pid} = cure_smt_process:start_solver(z3, 5000),

    Query = "(set-logic QF_LIA)\n(check-sat)\n",
    Result = cure_smt_process:execute_query(Pid, Query),

    case Result of
        {sat, _} ->
            cure_smt_process:stop_solver(Pid),
            io:format("✅~n"),
            ok;
        Other ->
            cure_smt_process:stop_solver(Pid),
            io:format("❌ Expected sat, got: ~p~n", [Other]),
            error(unexpected_result)
    end.

test_satisfiable_constraint() ->
    io:format("Testing satisfiable constraint... "),
    {ok, Pid} = cure_smt_process:start_solver(z3, 5000),

    % x > y and y > 0
    Query =
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (> x y))\n"
        "(assert (> y 0))\n"
        "(check-sat)\n"
        "(get-model)\n",

    Result = cure_smt_process:execute_query(Pid, Query),

    case Result of
        {sat, Lines} when length(Lines) > 0 ->
            cure_smt_process:stop_solver(Pid),
            io:format("✅ (model with ~p lines)~n", [length(Lines)]),
            ok;
        Other ->
            cure_smt_process:stop_solver(Pid),
            io:format("❌ Expected sat with model, got: ~p~n", [Other]),
            error(unexpected_result)
    end.

test_unsatisfiable_constraint() ->
    io:format("Testing unsatisfiable constraint... "),
    {ok, Pid} = cure_smt_process:start_solver(z3, 5000),

    % x > 0 and x < 0 (impossible)
    Query =
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(assert (> x 0))\n"
        "(assert (< x 0))\n"
        "(check-sat)\n",

    Result = cure_smt_process:execute_query(Pid, Query),

    case Result of
        {unsat, _} ->
            cure_smt_process:stop_solver(Pid),
            io:format("✅~n"),
            ok;
        Other ->
            cure_smt_process:stop_solver(Pid),
            io:format("❌ Expected unsat, got: ~p~n", [Other]),
            error(unexpected_result)
    end.

test_reset() ->
    io:format("Testing solver reset... "),
    {ok, Pid} = cure_smt_process:start_solver(z3, 5000),

    % First query
    Query1 = "(set-logic QF_LIA)\n(declare-const x Int)\n(check-sat)\n",
    {sat, _} = cure_smt_process:execute_query(Pid, Query1),

    % Reset
    ok = cure_smt_process:reset_solver(Pid),

    % Second query (should work after reset)
    Query2 = "(set-logic QF_LIA)\n(declare-const y Int)\n(check-sat)\n",
    {sat, _} = cure_smt_process:execute_query(Pid, Query2),

    cure_smt_process:stop_solver(Pid),
    io:format("✅~n"),
    ok.

test_statistics() ->
    io:format("Testing statistics... "),
    {ok, Pid} = cure_smt_process:start_solver(z3, 5000),

    % Execute a few queries
    Query = "(set-logic QF_LIA)\n(check-sat)\n",
    cure_smt_process:execute_query(Pid, Query),
    cure_smt_process:execute_query(Pid, Query),
    cure_smt_process:execute_query(Pid, Query),

    Stats = cure_smt_process:get_stats(Pid),
    QueryCount = maps:get(query_count, Stats),

    case QueryCount of
        3 ->
            cure_smt_process:stop_solver(Pid),
            io:format("✅ (query_count=~p)~n", [QueryCount]),
            ok;
        Other ->
            cure_smt_process:stop_solver(Pid),
            io:format("❌ Expected query_count=3, got: ~p~n", [Other]),
            error(unexpected_count)
    end.

test_translator_integration() ->
    io:format("Testing translator integration... "),
    {ok, Pid} = cure_smt_process:start_solver(z3, 5000),

    % Use translator to generate query
    Constraint = #binary_op_expr{
        op = '>',
        left = #identifier_expr{name = x, location = #location{}},
        right = #literal_expr{value = 0, location = #location{}},
        location = #location{}
    },
    Env = #{x => {type, int}},

    Query = cure_smt_translator:generate_query(Constraint, Env),
    QueryBin = iolist_to_binary(Query),

    Result = cure_smt_process:execute_query(Pid, QueryBin),

    case Result of
        {sat, _} ->
            cure_smt_process:stop_solver(Pid),
            io:format("✅~n"),
            ok;
        Other ->
            cure_smt_process:stop_solver(Pid),
            io:format("❌ Expected sat, got: ~p~n", [Other]),
            io:format("     Query was: ~s~n", [QueryBin]),
            error(unexpected_result)
    end.
