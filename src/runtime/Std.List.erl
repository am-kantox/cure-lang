%% Cure Standard Library - List Module (Temporary Erlang Implementation)
%% This is a temporary implementation until the Cure standard library can be compiled
-module('Std.List').

-moduledoc """
# Cure Standard Library - List Processing Module

Provides comprehensive list processing functionality for Cure programs.
This is a temporary Erlang implementation that will eventually be replaced
by pure Cure implementations once the compiler and standard library
are fully bootstrapped.

## Function Categories

### Higher-Order Functions
- `map/2` - Transform each element with a function
- `filter/2` - Select elements matching a predicate
- `find/2` - Search for first element matching predicate
- `zip_with/3` - Combine two lists element-wise with a function

### Reduction Functions
- `fold/3` - Reduce list to single value (left-associative)
- `foldl/3` - Left fold (same as fold/3)
- `foldr/3` - Right fold

### Basic Operations
- `head/1` - Get first element
- `tail/1` - Get all elements except first
- `length/1` - Count elements
- `reverse/1` - Reverse element order

## Type Signatures (Cure notation)

```cure
map :: (a -> b, List(a)) -> List(b)
filter :: (a -> Bool, List(a)) -> List(a)
fold :: (List(a), b, (a, b) -> b) -> b
zip_with :: (List(a), List(b), (a, b) -> c) -> List(c)
find :: (a -> Bool, List(a)) -> Option(a)
head :: List(a) -> a  // throws on empty list
tail :: List(a) -> List(a)
length :: List(a) -> Int
reverse :: List(a) -> List(a)
```

## Usage Examples

### Transformation
```cure
// Double all numbers
let doubled = map(fn x -> x * 2 end, [1, 2, 3])
// Result: [2, 4, 6]

// Convert to strings
let strings = map(show, [1, 2, 3])
// Result: ["1", "2", "3"]
```

### Filtering
```cure
// Get even numbers
let evens = filter(fn x -> x % 2 == 0 end, [1, 2, 3, 4])
// Result: [2, 4]

// Get non-empty strings
let nonEmpty = filter(fn s -> length(s) > 0 end, ["a", "", "b"])
// Result: ["a", "b"]
```

### Reduction
```cure
// Sum all numbers
let total = fold([1, 2, 3, 4], 0, fn x, acc -> x + acc end)
// Result: 10

// Concatenate strings
let joined = fold(["a", "b", "c"], "", fn x, acc -> acc ++ x end)
// Result: "abc"
```

### Searching
```cure
// Find first even number
let firstEven = find(fn x -> x % 2 == 0 end, [1, 3, 4, 5])
// Result: Some(4)

// Search in empty list
let notFound = find(fn _ -> true end, [])
// Result: None
```

## Implementation Notes

### Error Handling
- `head/1` throws an error on empty lists
- `find/2` returns Option types (Some/None)
- Other functions handle empty lists gracefully

### Performance Characteristics
- `map/2`, `filter/2`: O(n) time, O(n) space
- `fold/3`, `foldl/3`: O(n) time, O(1) space (tail-recursive)
- `foldr/3`: O(n) time, O(n) space (not tail-recursive)
- `head/1`, `tail/1`: O(1) time
- `length/1`: O(n) time
- `reverse/1`: O(n) time, O(n) space

### Argument Order
Function argument order is optimized for partial application and
piping in Cure:
- Functions come before lists where practical
- Accumulator is typically the middle argument in folds

## Migration Path

This Erlang implementation will be replaced by:
1. Pure Cure implementations in lib/std/list.cure
2. Compiler-generated optimized versions
3. Integration with Cure's type system and pattern matching

The API will remain stable during this transition.
""".

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
    % Handle both curried and non-curried functions
    Result =
        try
            % Try curried application: F(X)(Y)
            CurriedF = F(X),
            CurriedF(Y)
        catch
            _:_ ->
                % Fallback to direct application: F(X, Y)
                F(X, Y)
        end,
    [Result | zip_with(Xs, Ys, F)].

%% Fold function with different argument order for Cure compatibility
%% fold(List, InitialValue, Function)
fold([], Acc, _F) ->
    Acc;
fold([H | T], Acc, F) ->
    % Handle both curried and non-curried functions
    NewAcc =
        try
            % Try curried application: F(H)(Acc)
            CurriedF = F(H),
            CurriedF(Acc)
        catch
            _:_ ->
                % Fallback to direct application: F(H, Acc)
                F(H, Acc)
        end,
    fold(T, NewAcc, F).

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
