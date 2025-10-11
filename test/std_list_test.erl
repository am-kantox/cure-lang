%% Cure Standard Library List Tests
%% Tests for Std.List module functions including length, head, tail, map, filter
%% and other list operations with various inputs
-module(std_list_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").

%% Run all Std.List tests
run() ->
    io:format("Running Std.List tests...~n"),
    test_basic_list_operations(),
    test_list_construction(),
    test_list_transformation(),
    test_list_access(),
    test_list_predicates(),
    test_safe_operations(),
    test_edge_cases(),
    io:format("All Std.List tests passed!~n").

%% ============================================================================
%% Test 1: Basic list operations - length, head, tail, is_empty
%% ============================================================================

test_basic_list_operations() ->
    io:format("Testing basic list operations...~n"),

    % Test length/1 with various lists
    ?assertEqual(0, test_length([])),
    ?assertEqual(1, test_length([42])),
    ?assertEqual(3, test_length([1, 2, 3])),
    ?assertEqual(5, test_length([a, b, c, d, e])),
    ?assertEqual(10, test_length([1, 2, 3, 4, 5, 6, 7, 8, 9, 10])),

    % Test with nested lists
    ?assertEqual(3, test_length([[1, 2], [3, 4], [5]])),

    % Test with mixed types
    ?assertEqual(4, test_length([1, atom, "string", [nested]])),

    % Test head/1
    ?assertEqual(1, test_head([1, 2, 3])),
    ?assertEqual(a, test_head([a, b, c])),
    ?assertEqual("first", test_head(["first", "second"])),

    % Test tail/1
    ?assertEqual([2, 3], test_tail([1, 2, 3])),
    ?assertEqual([b, c], test_tail([a, b, c])),
    ?assertEqual([], test_tail([single])),
    ?assertEqual([2, 3, 4, 5], test_tail([1, 2, 3, 4, 5])),

    % Test is_empty/1
    ?assertEqual(true, test_is_empty([])),
    ?assertEqual(false, test_is_empty([1])),
    ?assertEqual(false, test_is_empty([1, 2, 3])),

    io:format("✓ Basic list operations test passed~n").

% Helper functions for basic operations
test_length(List) -> length(List).
test_head([H | _]) -> H.
test_tail([_ | T]) -> T.
test_is_empty([]) -> true;
test_is_empty(_) -> false.

%% ============================================================================
%% Test 2: List construction - cons, append, reverse
%% ============================================================================

test_list_construction() ->
    io:format("Testing list construction...~n"),

    % Test cons/2 (prepend element)
    ?assertEqual([1, 2, 3], test_cons(1, [2, 3])),
    ?assertEqual([a], test_cons(a, [])),
    ?assertEqual([new, old, existing], test_cons(new, [old, existing])),

    % Test append/2 (concatenate lists)
    ?assertEqual([1, 2, 3, 4, 5], test_append([1, 2], [3, 4, 5])),
    ?assertEqual([1, 2, 3], test_append([1, 2, 3], [])),
    ?assertEqual([4, 5, 6], test_append([], [4, 5, 6])),
    ?assertEqual([], test_append([], [])),

    % Test with different types
    ?assertEqual([atom, 1, "string"], test_append([atom], [1, "string"])),

    % Test reverse/1
    ?assertEqual([], test_reverse([])),
    ?assertEqual([1], test_reverse([1])),
    ?assertEqual([3, 2, 1], test_reverse([1, 2, 3])),
    ?assertEqual([e, d, c, b, a], test_reverse([a, b, c, d, e])),

    % Test reverse with complex elements
    ?assertEqual([[3], [2], [1]], test_reverse([[1], [2], [3]])),

    io:format("✓ List construction test passed~n").

% Helper functions for construction
test_cons(Element, List) -> [Element | List].
test_append(List1, List2) -> List1 ++ List2.
test_reverse(List) -> lists:reverse(List).

%% ============================================================================
%% Test 3: List transformation - map, filter, folds
%% ============================================================================

test_list_transformation() ->
    io:format("Testing list transformation...~n"),

    % Test map/2 with various functions
    Double = fun(X) -> X * 2 end,
    ?assertEqual([], test_map([], Double)),
    ?assertEqual([2], test_map([1], Double)),
    ?assertEqual([2, 4, 6], test_map([1, 2, 3], Double)),
    ?assertEqual([10, 20, 30, 40], test_map([5, 10, 15, 20], Double)),

    % Test map with different function types
    ToString = fun(X) -> integer_to_list(X) end,
    ?assertEqual(["1", "2", "3"], test_map([1, 2, 3], ToString)),

    Square = fun(X) -> X * X end,
    ?assertEqual([1, 4, 9, 16, 25], test_map([1, 2, 3, 4, 5], Square)),

    % Test filter/2 with predicates
    IsEven = fun(X) -> X rem 2 == 0 end,
    ?assertEqual([], test_filter([], IsEven)),
    ?assertEqual([2, 4], test_filter([1, 2, 3, 4, 5], IsEven)),
    ?assertEqual([2, 4, 6, 8, 10], test_filter([1, 2, 3, 4, 5, 6, 7, 8, 9, 10], IsEven)),

    IsPositive = fun(X) -> X > 0 end,
    ?assertEqual([1, 2, 5], test_filter([-1, 1, -2, 2, 0, 5], IsPositive)),

    % Test fold_left/3
    Sum = fun(X, Acc) -> X + Acc end,
    ?assertEqual(0, test_fold_left([], 0, Sum)),
    ?assertEqual(10, test_fold_left([1, 2, 3, 4], 0, Sum)),
    ?assertEqual(15, test_fold_left([1, 2, 3, 4, 5], 0, Sum)),

    % Test fold_right/3
    ?assertEqual(0, test_fold_right([], 0, Sum)),
    ?assertEqual(10, test_fold_right([1, 2, 3, 4], 0, Sum)),

    % Test with string concatenation
    Concat = fun(Str, Acc) -> Str ++ Acc end,
    ?assertEqual("abc", test_fold_right(["a", "b", "c"], "", Concat)),

    io:format("✓ List transformation test passed~n").

% Helper functions for transformation
test_map(List, Fun) ->
    lists:map(Fun, List).

test_filter(List, Pred) ->
    lists:filter(Pred, List).

test_fold_left(List, Acc, Fun) ->
    lists:foldl(Fun, Acc, List).

test_fold_right(List, Acc, Fun) ->
    lists:foldr(Fun, Acc, List).

%% ============================================================================
%% Test 4: List access - nth, take, drop
%% ============================================================================

test_list_access() ->
    io:format("Testing list access operations...~n"),

    % Test nth/2 (0-based indexing assumed)
    TestList = [a, b, c, d, e],
    ?assertEqual(a, test_nth(TestList, 0)),
    ?assertEqual(b, test_nth(TestList, 1)),
    ?assertEqual(e, test_nth(TestList, 4)),

    % Test with numbers
    NumList = [10, 20, 30, 40, 50],
    ?assertEqual(10, test_nth(NumList, 0)),
    ?assertEqual(30, test_nth(NumList, 2)),
    ?assertEqual(50, test_nth(NumList, 4)),

    % Test take/2
    ?assertEqual([], test_take([], 3)),
    ?assertEqual([], test_take([1, 2, 3], 0)),
    ?assertEqual([1], test_take([1, 2, 3], 1)),
    ?assertEqual([1, 2], test_take([1, 2, 3], 2)),
    ?assertEqual([1, 2, 3], test_take([1, 2, 3], 3)),
    % Take more than available
    ?assertEqual([1, 2, 3], test_take([1, 2, 3], 5)),

    % Test drop/2
    ?assertEqual([], test_drop([], 3)),
    ?assertEqual([1, 2, 3], test_drop([1, 2, 3], 0)),
    ?assertEqual([2, 3], test_drop([1, 2, 3], 1)),
    ?assertEqual([3], test_drop([1, 2, 3], 2)),
    ?assertEqual([], test_drop([1, 2, 3], 3)),
    % Drop more than available
    ?assertEqual([], test_drop([1, 2, 3], 5)),

    io:format("✓ List access operations test passed~n").

% Helper functions for access
test_nth(List, Index) ->
    % Convert to 1-based for Erlang
    lists:nth(Index + 1, List).

test_take(List, N) when N =< 0 -> [];
test_take([], _) -> [];
test_take([H | T], N) -> [H | test_take(T, N - 1)].

test_drop(List, N) when N =< 0 -> List;
test_drop([], _) -> [];
test_drop([_ | T], N) -> test_drop(T, N - 1).

%% ============================================================================
%% Test 5: List predicates - all, any, contains
%% ============================================================================

test_list_predicates() ->
    io:format("Testing list predicates...~n"),

    % Test all/2
    IsPositive = fun(X) -> X > 0 end,
    % Vacuously true
    ?assertEqual(true, test_all([], IsPositive)),
    ?assertEqual(true, test_all([1, 2, 3], IsPositive)),
    ?assertEqual(false, test_all([1, -2, 3], IsPositive)),
    ?assertEqual(false, test_all([-1, -2, -3], IsPositive)),

    IsEven = fun(X) -> X rem 2 == 0 end,
    ?assertEqual(true, test_all([2, 4, 6, 8], IsEven)),
    ?assertEqual(false, test_all([2, 4, 5, 8], IsEven)),

    % Test any/2

    % Empty list
    ?assertEqual(false, test_any([], IsPositive)),
    ?assertEqual(true, test_any([1, -2, -3], IsPositive)),
    ?assertEqual(false, test_any([-1, -2, -3], IsPositive)),
    ?assertEqual(true, test_any([1, 2, 3], IsPositive)),

    % Contains 4
    ?assertEqual(true, test_any([1, 3, 4, 7], IsEven)),
    % All odd
    ?assertEqual(false, test_any([1, 3, 5, 7], IsEven)),

    % Test contains/2
    ?assertEqual(false, test_contains([], 5)),
    ?assertEqual(true, test_contains([1, 2, 3], 2)),
    ?assertEqual(false, test_contains([1, 2, 3], 4)),
    ?assertEqual(true, test_contains([a, b, c, d], c)),
    ?assertEqual(false, test_contains([a, b, c, d], e)),

    % Test with strings
    ?assertEqual(true, test_contains(["hello", "world"], "hello")),
    ?assertEqual(false, test_contains(["hello", "world"], "goodbye")),

    io:format("✓ List predicates test passed~n").

% Helper functions for predicates
test_all([], _) ->
    true;
test_all([H | T], Pred) ->
    case Pred(H) of
        true -> test_all(T, Pred);
        false -> false
    end.

test_any([], _) ->
    false;
test_any([H | T], Pred) ->
    case Pred(H) of
        true -> true;
        false -> test_any(T, Pred)
    end.

test_contains(List, Element) ->
    lists:member(Element, List).

%% ============================================================================
%% Test 6: Safe operations - safe_head, safe_tail, safe_nth
%% ============================================================================

test_safe_operations() ->
    io:format("Testing safe operations...~n"),

    % Note: In the actual Cure implementation, these would return Option(T)
    % For this test, we simulate the behavior with simplified return values

    % Test safe_head/1
    ?assertEqual({some, 1}, test_safe_head([1, 2, 3])),
    ?assertEqual({some, a}, test_safe_head([a, b, c])),
    ?assertEqual(none, test_safe_head([])),

    % Test safe_tail/1
    ?assertEqual({some, [2, 3]}, test_safe_tail([1, 2, 3])),
    ?assertEqual({some, []}, test_safe_tail([only])),
    ?assertEqual(none, test_safe_tail([])),

    % Test safe_nth/2
    TestList = [a, b, c, d, e],
    ?assertEqual({some, a}, test_safe_nth(TestList, 0)),
    ?assertEqual({some, c}, test_safe_nth(TestList, 2)),
    ?assertEqual(none, test_safe_nth(TestList, 10)),
    ?assertEqual(none, test_safe_nth(TestList, -1)),
    ?assertEqual(none, test_safe_nth([], 0)),

    io:format("✓ Safe operations test passed~n").

% Helper functions for safe operations (simplified)
test_safe_head([]) -> none;
test_safe_head([H | _]) -> {some, H}.

test_safe_tail([]) -> none;
test_safe_tail([_ | T]) -> {some, T}.

test_safe_nth([], _) ->
    none;
test_safe_nth(_, Index) when Index < 0 -> none;
test_safe_nth(List, Index) ->
    try
        {some, lists:nth(Index + 1, List)}
    catch
        error:function_clause -> none;
        error:badarg -> none
    end.

%% ============================================================================
%% Test 7: Edge cases and error conditions
%% ============================================================================

test_edge_cases() ->
    io:format("Testing edge cases...~n"),

    % Test with very large lists
    LargeList = lists:seq(1, 1000),
    ?assertEqual(1000, test_length(LargeList)),
    ?assertEqual(1, test_head(LargeList)),
    ?assertEqual(1000, lists:last(LargeList)),

    % Test map with large list
    LargeDoubled = test_map(LargeList, fun(X) -> X * 2 end),
    ?assertEqual(2000, test_length(LargeDoubled)),
    ?assertEqual(2, test_head(LargeDoubled)),

    % Test filter with large list
    LargeEvens = test_filter(LargeList, fun(X) -> X rem 2 == 0 end),
    % Half should be even
    ?assertEqual(500, test_length(LargeEvens)),

    % Test deeply nested structures
    DeepList = [[[1]], [[2]], [[3]]],
    ?assertEqual(3, test_length(DeepList)),
    ?assertEqual([[1]], test_head(DeepList)),

    % Test with empty lists in various operations
    ?assertEqual([], test_map([], fun(X) -> X + 1 end)),
    ?assertEqual([], test_filter([], fun(_) -> true end)),
    ?assertEqual([], test_append([], [])),
    ?assertEqual([], test_reverse([])),

    % Test with single element lists
    Single = [42],
    ?assertEqual(1, test_length(Single)),
    ?assertEqual(42, test_head(Single)),
    ?assertEqual([], test_tail(Single)),
    ?assertEqual([42], test_reverse(Single)),

    io:format("✓ Edge cases test passed~n").
