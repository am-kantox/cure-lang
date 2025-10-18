-module(test_direct_fold).
-export([run/0]).

run() ->
    io:format("Testing Std.List.fold directly...~n"),

    % Test with a simple list and function
    List = [1, 2, 3],
    Init = 0,

    % Try to create a simple adding function in Erlang
    AddFunc = fun(X) ->
        fun(Acc) -> X + Acc end
    end,

    io:format("Calling 'Std.List':fold([1,2,3], 0, AddFunc)...~n"),
    try
        Result = 'Std.List':fold(List, Init, AddFunc),
        io:format("Result: ~p (type: ~p)~n", [Result, type_of(Result)])
    catch
        Error:Reason:Stack ->
            io:format("Error calling fold: ~p:~p~n", [Error, Reason]),
            io:format("Stack: ~p~n", [Stack])
    end.

type_of(X) when is_integer(X) -> integer;
type_of(X) when is_atom(X) -> atom;
type_of(X) when is_list(X) -> list;
type_of(X) when is_tuple(X) -> tuple;
type_of(X) when is_function(X) -> function;
type_of(_) -> unknown.
