-module(test_debug).
-export([run/0]).

run() ->
    io:format("Loading DebugFold module...~n"),
    case code:load_file('DebugFold') of
        {module, DebugFold} ->
            io:format("Module loaded successfully~n"),

            io:format("Testing simple operation...~n"),
            Result1 = DebugFold:test_simple(),
            io:format("test_simple() result: ~p~n", [Result1]),

            io:format("Testing fold operation...~n"),
            Result2 = DebugFold:test_fold(),
            io:format("test_fold() result: ~p~n", [Result2]);
        Error ->
            io:format("Failed to load module: ~p~n", [Error])
    end.
