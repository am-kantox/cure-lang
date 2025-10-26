-module(test_atom_runtime).
-export([run/0]).

run() ->
    io:format("Testing Atom bridge at runtime...~n"),

    % Test atom return
    Result1 = 'AtomSimpleTest':test1(),
    io:format("  test1() returned: ~p~n", [Result1]),
    io:format("  Is atom? ~p~n", [is_atom(Result1)]),
    io:format("  Expected: hello, Got: ~p, Match: ~p~n", [Result1, Result1 =:= hello]),

    case Result1 =:= hello of
        true ->
            io:format("~n✓ SUCCESS! Atom bridge works correctly!~n"),
            io:format("  Cure Atom type -> Erlang atom: WORKING~n");
        false ->
            io:format("~n✗ FAILED! Expected hello, got ~p~n", [Result1]),
            halt(1)
    end.
