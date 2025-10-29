-module(smt_parser_test).
-export([run/0]).

run() ->
    io:format("~n=== SMT Parser Tests ===~n~n"),

    Tests = [
        fun test_parse_simple_model/0,
        fun test_parse_empty_model/0,
        fun test_parse_mixed_types/0,
        fun test_parse_real_z3_output/0,
        fun test_end_to_end_with_z3/0
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

test_parse_simple_model() ->
    io:format("Testing simple model parsing... "),
    Lines = [
        <<"(">>,
        <<"  (define-fun x () Int 5)">>,
        <<"  (define-fun y () Int 3)">>,
        <<")">>
    ],
    {ok, Model} = cure_smt_parser:parse_model(Lines),
    case Model of
        #{x := 5, y := 3} ->
            io:format("✅~n"),
            ok;
        Other ->
            io:format("❌ Expected #{x => 5, y => 3}, got ~p~n", [Other]),
            error(unexpected_model)
    end.

test_parse_empty_model() ->
    io:format("Testing empty model... "),
    {ok, Model} = cure_smt_parser:parse_model([]),
    case Model of
        Empty when map_size(Empty) =:= 0 ->
            io:format("✅~n"),
            ok;
        Other ->
            io:format("❌ Expected empty map, got ~p~n", [Other]),
            error(unexpected_model)
    end.

test_parse_mixed_types() ->
    io:format("Testing mixed types... "),
    Lines = [
        <<"(">>,
        <<"  (define-fun x () Int 42)">>,
        <<"  (define-fun flag () Bool true)">>,
        <<"  (define-fun ratio () Real 3.14)">>,
        <<")">>
    ],
    {ok, Model} = cure_smt_parser:parse_model(Lines),
    case Model of
        #{x := 42, flag := true, ratio := 3.14} ->
            io:format("✅~n"),
            ok;
        Other ->
            io:format("❌ Expected #{x => 42, flag => true, ratio => 3.14}, got ~p~n", [Other]),
            error(unexpected_model)
    end.

test_parse_real_z3_output() ->
    io:format("Testing real Z3 output format... "),
    % Actual Z3 output format (from our earlier test)
    Lines = [
        <<"(">>,
        <<"  (define-fun y () Int">>,
        <<"    1)">>,
        <<"  (define-fun x () Int">>,
        <<"    2)">>,
        <<")">>
    ],
    {ok, Model} = cure_smt_parser:parse_model(Lines),

    % Should extract x and y
    HasX = maps:is_key(x, Model),
    HasY = maps:is_key(y, Model),

    case {HasX, HasY} of
        {true, true} ->
            io:format("✅ (x=~p, y=~p)~n", [maps:get(x, Model), maps:get(y, Model)]),
            ok;
        _ ->
            io:format("❌ Expected x and y in model, got ~p~n", [Model]),
            error(missing_variables)
    end.

test_end_to_end_with_z3() ->
    io:format("Testing end-to-end with Z3... "),
    % Start solver, execute query, parse result
    {ok, Pid} = cure_smt_process:start_solver(z3, 5000),

    % Query that will produce a model
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
            % Try to parse the model
            case cure_smt_parser:parse_model(Lines) of
                {ok, Model} when map_size(Model) > 0 ->
                    cure_smt_process:stop_solver(Pid),
                    io:format("✅ (parsed ~p variables)~n", [map_size(Model)]),
                    ok;
                {ok, Empty} ->
                    cure_smt_process:stop_solver(Pid),
                    io:format("❌ Model parsed but empty. Lines were: ~p~n", [Lines]),
                    error(empty_model);
                {error, Reason} ->
                    cure_smt_process:stop_solver(Pid),
                    io:format("❌ Parse failed: ~p~n", [Reason]),
                    error(parse_failed)
            end;
        Other ->
            cure_smt_process:stop_solver(Pid),
            io:format("❌ Expected sat with model, got: ~p~n", [Other]),
            error(unexpected_result)
    end.
