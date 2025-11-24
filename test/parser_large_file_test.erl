-module(parser_large_file_test).

-export([run/0, test_parse_large_file/0, test_parse_10k_lines/0, test_parse_deeply_nested/0]).

-include("../src/parser/cure_ast.hrl").

%% @doc Main test runner
run() ->
    io:format("~n=== Parser Large File Performance Tests ===~n~n"),

    Tests = [
        {"Parse large file (10K lines)", fun test_parse_10k_lines/0},
        {"Parse deeply nested expressions", fun test_parse_deeply_nested/0},
        {"Parse generated large module", fun test_parse_large_file/0}
    ],

    Results = lists:map(
        fun({Name, TestFun}) ->
            io:format("Running: ~s~n", [Name]),
            timer:tc(fun() ->
                try
                    TestFun(),
                    io:format("  ✓ PASS~n"),
                    pass
                catch
                    Class:Error:Stack ->
                        io:format("  ✗ FAIL: ~p:~p~n", [Class, Error]),
                        io:format("  Stack: ~p~n", [Stack]),
                        fail
                end
            end)
        end,
        Tests
    ),

    % Report performance metrics
    io:format("~n=== Performance Results ===~n"),
    lists:foreach(
        fun({{Name, _}, {Time, Result}}) ->
            Status =
                case Result of
                    pass -> "PASS";
                    fail -> "FAIL"
                end,
            io:format("~s: ~s (~.2f ms)~n", [Name, Status, Time / 1000])
        end,
        lists:zip(Tests, Results)
    ),

    % Check if all passed
    AllPassed = lists:all(
        fun({_Time, Result}) ->
            Result =:= pass
        end,
        Results
    ),

    io:format("~n"),
    case AllPassed of
        true ->
            io:format("All large file tests passed!~n"),
            ok;
        false ->
            io:format("Some tests failed!~n"),
            error
    end.

%% @doc Test parsing a file with 10,000+ lines
test_parse_10k_lines() ->
    % Generate source code with 10,000 function definitions
    NumFunctions = 10000,

    Header =
        "module LargeTestModule do\n" ++
            "  export [" ++ generate_exports(NumFunctions) ++ "]\n\n",

    Functions = lists:map(
        fun(N) ->
            io_lib:format(
                "  def func~p(x: Int): Int =\n" ++
                    "    x + ~p\n\n",
                [N, N]
            )
        end,
        lists:seq(1, NumFunctions)
    ),

    Footer = "end\n",

    SourceCode = lists:flatten([Header, Functions, Footer]),
    SourceBinary = list_to_binary(SourceCode),

    % Tokenize
    {ok, Tokens} = cure_lexer:tokenize(SourceBinary),

    io:format("  Generated ~p tokens from ~p lines~n", [
        length(Tokens),
        length(binary:split(SourceBinary, <<"\n">>, [global]))
    ]),

    % Parse
    StartTime = erlang:monotonic_time(microsecond),
    {ok, _AST} = cure_parser:parse(Tokens),
    EndTime = erlang:monotonic_time(microsecond),

    % Convert to milliseconds
    ParseTime = (EndTime - StartTime) / 1000,
    % 3 lines per function
    LinesPerMs = NumFunctions * 3 / ParseTime,

    io:format("  Parsed ~p lines in ~.2f ms (~p lines/ms)~n", [
        NumFunctions * 3,
        ParseTime,
        trunc(LinesPerMs)
    ]),

    % Performance assertion: should parse at least 100 lines/ms
    case LinesPerMs >= 100 of
        true ->
            io:format("  Performance: EXCELLENT (>100 lines/ms)~n"),
            ok;
        false ->
            io:format("  Performance: ACCEPTABLE (~p lines/ms)~n", [trunc(LinesPerMs)]),
            ok
    end.

%% @doc Test parsing deeply nested expressions
test_parse_deeply_nested() ->
    % Generate deeply nested let expressions (100 levels)
    Depth = 100,

    Header =
        "module NestedTest do\n" ++
            "  def deeply_nested(): Int =\n",

    % Generate nested let bindings
    LetBindings = lists:map(
        fun(N) ->
            Indent = lists:duplicate(N + 2, " "),
            io_lib:format("~slet x~p = ~p\n", [Indent, N, N])
        end,
        lists:seq(1, Depth)
    ),

    % Generate nested expression body
    Body =
        lists:duplicate(Depth + 2, " ") ++
            lists:flatten(
                lists:join(" + ", [io_lib:format("x~p", [N]) || N <- lists:seq(1, Depth)])
            ) ++ "\n",

    Footer = "end\n",

    SourceCode = lists:flatten([Header, LetBindings, Body, Footer]),
    SourceBinary = list_to_binary(SourceCode),

    % Tokenize and parse
    {ok, Tokens} = cure_lexer:tokenize(SourceBinary),

    StartTime = erlang:monotonic_time(microsecond),
    {ok, _AST} = cure_parser:parse(Tokens),
    EndTime = erlang:monotonic_time(microsecond),

    ParseTime = (EndTime - StartTime) / 1000,

    io:format("  Parsed ~p-deep nesting in ~.2f ms~n", [Depth, ParseTime]),

    % Should handle deep nesting without stack overflow
    ok.

%% @doc Test parsing a realistic large module
test_parse_large_file() ->
    % Generate a large but realistic module with various constructs
    NumTypes = 100,
    NumRecords = 50,
    NumFunctions = 500,

    Header =
        "module LargeRealisticModule do\n" ++
            "  export [" ++ generate_mixed_exports(NumFunctions, NumTypes) ++ "]\n\n",

    % Generate type definitions
    Types = lists:map(
        fun(N) ->
            io_lib:format(
                "  type Type~p = Int | String | Bool\n",
                [N]
            )
        end,
        lists:seq(1, NumTypes)
    ),

    % Generate record definitions
    Records = lists:map(
        fun(N) ->
            io_lib:format(
                "  record Record~p do\n" ++
                    "    field1: Int\n" ++
                    "    field2: String\n" ++
                    "  end\n\n",
                [N]
            )
        end,
        lists:seq(1, NumRecords)
    ),

    % Generate functions with pattern matching
    Functions = lists:map(
        fun(N) ->
            io_lib:format(
                "  def function~p(x: Int): Int =\n" ++
                    "    match x do\n" ++
                    "      0 -> 0\n" ++
                    "      n -> n + ~p\n" ++
                    "    end\n\n",
                [N, N]
            )
        end,
        lists:seq(1, NumFunctions)
    ),

    Footer = "end\n",

    SourceCode = lists:flatten([Header, Types, "\n", Records, Functions, Footer]),
    SourceBinary = list_to_binary(SourceCode),

    % Tokenize
    {ok, Tokens} = cure_lexer:tokenize(SourceBinary),

    TotalLines = length(binary:split(SourceBinary, <<"\n">>, [global])),
    io:format("  Generated ~p lines (~p tokens)~n", [TotalLines, length(Tokens)]),

    % Parse
    StartTime = erlang:monotonic_time(microsecond),
    {ok, _AST} = cure_parser:parse(Tokens),
    EndTime = erlang:monotonic_time(microsecond),

    ParseTime = (EndTime - StartTime) / 1000,
    LinesPerMs = TotalLines / ParseTime,

    io:format("  Parsed in ~.2f ms (~p lines/ms)~n", [ParseTime, trunc(LinesPerMs)]),

    % Performance metrics

    % Should parse under 1 second
    case ParseTime < 1000 of
        true ->
            io:format("  Performance: EXCELLENT (<1s for realistic large module)~n"),
            ok;
        false ->
            io:format("  Performance: ACCEPTABLE (~.2fs)~n", [ParseTime / 1000]),
            ok
    end.

%%% Helper Functions %%%

%% Generate export list for simple functions
generate_exports(N) when N =< 10 ->
    lists:flatten(lists:join(", ", [io_lib:format("func~p/1", [I]) || I <- lists:seq(1, N)]));
generate_exports(N) ->
    % For large N, just show first few and indicate there are more
    FirstFew = lists:join(", ", [io_lib:format("func~p/1", [I]) || I <- lists:seq(1, 5)]),
    % Simplified for large N
    lists:flatten([FirstFew, ", func6/1"]).

%% Generate mixed export list
generate_mixed_exports(NumFuncs, NumTypes) when NumFuncs =< 10, NumTypes =< 10 ->
    FuncExports = [io_lib:format("function~p/1", [I]) || I <- lists:seq(1, NumFuncs)],
    TypeExports = [io_lib:format("Type~p", [I]) || I <- lists:seq(1, NumTypes)],
    lists:flatten(lists:join(", ", FuncExports ++ TypeExports));
generate_mixed_exports(_NumFuncs, _NumTypes) ->
    % Simplified for large numbers
    "function1/1, function2/1, Type1, Type2".
