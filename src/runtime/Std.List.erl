%% Cure Standard Library - List Module (Temporary Erlang Implementation)
%% This is a temporary implementation until the Cure standard library can be compiled
-module('Std.List').

%% Export the functions that are being called by compiled Cure code
-export([
    zip_with/3,
    fold/3,
    map/2,
    filter/2,
    head/1,
    tail/1,
    length/1,
    reverse/1,
    find/2,
    foldl/3,
    foldr/3
]).

%% Zip two lists with a function
zip_with([], [], _F) ->
    [];
zip_with([], _, _F) ->
    [];
zip_with(_, [], _F) ->
    [];
zip_with([X | Xs], [Y | Ys], F) ->
    [F(X, Y) | zip_with(Xs, Ys, F)].

%% Fold function with different argument order for Cure compatibility
%% fold(List, InitialValue, Function)
fold([], Acc, _F) ->
    Acc;
fold([H | T], Acc, F) ->
    fold(T, F(H, Acc), F).

%% Map function over list
map(_F, []) ->
    [];
map(F, [H | T]) ->
    [F(H) | map(F, T)].

%% Filter list based on predicate
filter(_Pred, []) ->
    [];
filter(Pred, [H | T]) ->
    case Pred(H) of
        true ->
            [H | filter(Pred, T)];
        false ->
            filter(Pred, T)
    end.

%% Get head of list
head([]) ->
    erlang:error("Empty list");
head([H | _]) ->
    H.

%% Get tail of list
tail([]) ->
    [];
tail([_ | T]) ->
    T.

%% Get length of list
length(List) ->
    erlang:length(List).

%% Reverse list
reverse(List) ->
    lists:reverse(List).

%% Find element in list
find(_Pred, []) ->
    'None';
find(Pred, [H | T]) ->
    case Pred(H) of
        true ->
            {'Some', H};
        false ->
            find(Pred, T)
    end.

%% Left fold over list
foldl(_F, Acc, []) ->
    Acc;
foldl(F, Acc, [H | T]) ->
    foldl(F, F(H, Acc), T).

%% Right fold over list
foldr(_F, Acc, []) ->
    Acc;
foldr(F, Acc, [H | T]) ->
    F(H, foldr(F, Acc, T)).
