-module(test_minimal).
-export([run/0]).

run() ->
    io:format("Loading MinimalFold module...~n"),
    case code:load_file('MinimalFold') of
        {module, MinimalFold} ->
            io:format("Module loaded successfully~n"),
            io:format("Testing local fold operation...~n"),
            Result = MinimalFold:test_local_fold(),
            io:format("test_local_fold() result: ~p~n", [Result]);
        Error ->
            io:format("Failed to load module: ~p~n", [Error])
    end.
