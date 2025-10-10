%% Minimal Std module stub for Cure language
%% Provides essential functions for dependent types examples
-module('Std').

-export([
    print/1, show/1, map/2, fold/3, zip_with/3,
    head/1, tail/1, cons/2, append/2, length/1
]).

%% Print function - outputs to stdout
print(Value) ->
    io:format("~p~n", [Value]),
    ok.

%% Show function - converts values to string representation
show({'Ok', Value}) ->
    % Handle Ok results by showing the inner value
    show(Value);
show({'Error', Reason}) ->
    % Handle Error results
    "Error(" ++ show(Reason) ++ ")";
show({'Some', Value}) ->
    % Handle Some options
    "Some(" ++ show(Value) ++ ")";
show('None') ->
    % Handle None option
    "None";
show(Value) when is_atom(Value) ->
    atom_to_list(Value);
show(Value) when is_integer(Value) ->
    integer_to_list(Value);
show(Value) when is_float(Value) ->
    float_to_list(Value);
show(Value) when is_list(Value) ->
    % Simple list representation
    "[" ++ string:join([show(Item) || Item <- Value], ", ") ++ "]";
show(Value) when is_tuple(Value) ->
    % Simple tuple representation
    case tuple_size(Value) of
        0 -> "{}";
        1 -> "{" ++ show(element(1, Value)) ++ "}";
        2 -> "{" ++ show(element(1, Value)) ++ ", " ++ show(element(2, Value)) ++ "}";
        3 -> "{" ++ show(element(1, Value)) ++ ", " ++ show(element(2, Value)) ++ ", " ++ show(element(3, Value)) ++ "}";
        4 -> "{" ++ show(element(1, Value)) ++ ", " ++ show(element(2, Value)) ++ ", " ++ show(element(3, Value)) ++ ", " ++ show(element(4, Value)) ++ "}";
        _ -> "{" ++ show(element(1, Value)) ++ ", " ++ show(element(2, Value)) ++ ", " ++ show(element(3, Value)) ++ ", " ++ show(element(4, Value)) ++ ", ...}"
    end;
show(_Value) ->
    "unknown".

%% Map function - applies a function to each element of a list
map([], _Fun) -> [];
map([H|T], Fun) -> [Fun(H) | map(T, Fun)].

%% Fold function - reduces a list using an accumulator (left fold)
%% Arguments: List, InitialValue, Function (to match Cure piped calling convention)
fold([], Acc, _Fun) -> Acc;
fold([H|T], Acc, Fun) -> fold(T, Fun(H, Acc), Fun).

%% Zip with function - combines two lists using a function
%% Arguments: List1, List2, Fun (to match Cure calling convention)
zip_with([], [], _Fun) -> [];
zip_with([], _, _Fun) -> [];
zip_with(_, [], _Fun) -> [];
zip_with([H1|T1], [H2|T2], Fun) -> [Fun(H1, H2) | zip_with(T1, T2, Fun)].

%% List head
head([H|_]) -> H.

%% List tail
tail([_|T]) -> T.

%% List cons (prepend)
cons(H, T) -> [H|T].

%% List append
append([], L2) -> L2;
append([H|T], L2) -> [H | append(T, L2)].

%% List length
length(L) -> erlang:length(L).