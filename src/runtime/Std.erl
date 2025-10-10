%% Cure Standard Library - Main Module (Temporary Erlang Implementation)
%% This re-exports functions from various standard library modules
-module('Std').

%% Re-export list functions from Std.List
-export([
    % List functions
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
    foldr/3,

    % Types (for import compatibility) - these are just dummy functions
    % In real Cure, these would be type constructors
    'List'/1,
    'Result'/2
]).

%% Re-export list functions by delegating to Std.List
zip_with(List1, List2, Fun) ->
    'Std.List':zip_with(List1, List2, Fun).

fold(List, Acc, Fun) ->
    'Std.List':fold(List, Acc, Fun).

map(Fun, List) ->
    'Std.List':map(Fun, List).

filter(Pred, List) ->
    'Std.List':filter(Pred, List).

head(List) ->
    'Std.List':head(List).

tail(List) ->
    'Std.List':tail(List).

length(List) ->
    'Std.List':length(List).

reverse(List) ->
    'Std.List':reverse(List).

find(Pred, List) ->
    'Std.List':find(Pred, List).

foldl(Fun, Acc, List) ->
    'Std.List':foldl(Fun, Acc, List).

foldr(Fun, Acc, List) ->
    'Std.List':foldr(Fun, Acc, List).

%% Type constructor dummies (these don't do anything at runtime)
'List'(_ElementType) ->
    list.

'Result'(_OkType, _ErrorType) ->
    result.
