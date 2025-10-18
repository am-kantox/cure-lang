-module(test_fold).
-export([run/0]).

run() ->
    io:format("Loading FoldTest module...~n"),
    case code:load_file('FoldTest') of
        {module, FoldTest} ->
            io:format("Module loaded successfully~n"),
            io:format("Calling FoldTest:demo()...~n"),
            Result = FoldTest:demo(),
            io:format("Result: ~p~n", [Result]);
        Error ->
            io:format("Failed to load module: ~p~n", [Error])
    end.
