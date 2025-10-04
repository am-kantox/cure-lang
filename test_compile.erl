#!/usr/bin/env escript
-include("src/cure_cli.erl").

main(_) ->
    Options = #compile_options{verbose = true},
    case cure_cli:compile_file("lib/examples/simple_demo.cure", Options) of
        {ok, OutputFile} ->
            io:format("Successfully compiled -> ~s~n", [OutputFile]);
        {error, Reason} ->
            io:format("Compilation failed: ~p~n", [Reason])
    end.