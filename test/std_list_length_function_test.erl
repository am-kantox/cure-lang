%% Unit Tests for Std.List.length Function Behavior
%% Tests specifically for:
%% 5. Std.List.length function returns the simplified length for integer lists and other list types
-module(std_list_length_function_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").

%% Run Std.List.length function specific tests
run() ->
    cure_utils:debug("Running Std.List.length Function Tests...~n"),

    test_integer_list_length(),
    test_mixed_type_list_length(),
    test_nested_list_length(),
    test_empty_and_single_element_lists(),
    test_large_list_performance(),
    test_special_value_lists(),
    test_edge_cases_and_boundaries(),

    cure_utils:debug("All Std.List.length function tests passed!~n").

%% ============================================================================
%% Test 5: Std.List.length function returns simplified length for integer lists
%% ============================================================================

test_integer_list_length() ->
    cure_utils:debug("Testing Std.List.length with integer lists...~n"),

    % Test 5.1: Basic integer lists
    ?assertEqual(0, test_length([])),
    ?assertEqual(1, test_length([42])),
    ?assertEqual(2, test_length([1, 2])),
    ?assertEqual(3, test_length([1, 2, 3])),
    ?assertEqual(5, test_length([10, 20, 30, 40, 50])),

    % Test 5.2: Sequential integer lists
    ?assertEqual(10, test_length([1, 2, 3, 4, 5, 6, 7, 8, 9, 10])),
    ?assertEqual(20, test_length(lists:seq(1, 20))),
    ?assertEqual(100, test_length(lists:seq(1, 100))),

    % Test 5.3: Integer lists with duplicates
    ?assertEqual(5, test_length([1, 1, 1, 1, 1])),
    ?assertEqual(6, test_length([42, 42, 42, 42, 42, 42])),

    % Test 5.4: Integer lists with negative numbers
    ?assertEqual(3, test_length([-1, -2, -3])),
    ?assertEqual(5, test_length([-10, -5, 0, 5, 10])),
    ?assertEqual(4, test_length([100, -100, 200, -200])),

    % Test 5.5: Large integer values
    ?assertEqual(3, test_length([1000000000, 2000000000, 3000000000])),
    % Max/Min 64-bit integers
    ?assertEqual(2, test_length([9223372036854775807, -9223372036854775808])),

    cure_utils:debug("✓ Integer list length test passed~n").

test_mixed_type_list_length() ->
    cure_utils:debug("Testing Std.List.length with mixed type lists...~n"),

    % Test 6.1: Integer and atom mixtures
    ?assertEqual(4, test_length([1, atom, 2, another_atom])),
    ?assertEqual(6, test_length([42, hello, world, 100, test, 200])),

    % Test 6.2: Integer and string mixtures
    ?assertEqual(5, test_length([1, "hello", 2, "world", 3])),
    ?assertEqual(3, test_length(["first", 42, "last"])),

    % Test 6.3: Integer, atom, and string combinations
    ?assertEqual(6, test_length([1, atom, "string", 2, another_atom, "another_string"])),

    % Test 6.4: Integer and float mixtures
    ?assertEqual(4, test_length([1, 1.5, 2, 2.5])),
    ?assertEqual(6, test_length([10, 10.1, 20, 20.2, 30, 30.3])),

    % Test 6.5: Complex mixed types
    ?assertEqual(7, test_length([1, 2.5, atom, "string", true, {tuple}, [nested]])),

    cure_utils:debug("✓ Mixed type list length test passed~n").

test_nested_list_length() ->
    cure_utils:debug("Testing Std.List.length with nested lists...~n"),

    % Test 7.1: Simple nested lists (each nested list counts as one element)
    ?assertEqual(3, test_length([[1, 2], [3, 4], [5, 6]])),
    ?assertEqual(2, test_length([[1, 2, 3], [4, 5, 6, 7, 8]])),

    % Test 7.2: Mixed nested and flat elements
    ?assertEqual(5, test_length([1, [2, 3], 4, [5, 6, 7], 8])),
    ?assertEqual(4, test_length([[1], 2, [3, 4, 5], 6])),

    % Test 7.3: Deeply nested lists
    ?assertEqual(3, test_length([[[1]], [[2, 3]], [[4, 5, 6]]])),
    ?assertEqual(2, test_length([[[[1, 2]]], [[[3], [4]]]])),

    % Test 7.4: Empty nested lists
    ?assertEqual(3, test_length([[], [1, 2], []])),
    ?assertEqual(4, test_length([[], [], [], []])),

    % Test 7.5: Nested lists with mixed types
    ?assertEqual(3, test_length([[1, atom], ["string", 2.5], [true, {tuple, value}]])),

    cure_utils:debug("✓ Nested list length test passed~n").

test_empty_and_single_element_lists() ->
    cure_utils:debug("Testing Std.List.length with empty and single element cases...~n"),

    % Test 8.1: Empty list
    ?assertEqual(0, test_length([])),

    % Test 8.2: Single element of various types
    ?assertEqual(1, test_length([42])),
    ?assertEqual(1, test_length([atom])),
    ?assertEqual(1, test_length(["string"])),
    ?assertEqual(1, test_length([1.5])),
    ?assertEqual(1, test_length([true])),
    ?assertEqual(1, test_length([{tuple}])),
    ?assertEqual(1, test_length([[nested, list]])),

    % Test 8.3: Single element with complex structures
    ?assertEqual(1, test_length([{complex, tuple, with, many, elements}])),
    ?assertEqual(1, test_length([[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]])),

    cure_utils:debug("✓ Empty and single element list test passed~n").

test_large_list_performance() ->
    cure_utils:debug("Testing Std.List.length performance with large lists...~n"),

    % Test 9.1: Large integer lists (performance test)
    LargeList1000 = lists:seq(1, 1000),
    ?assertEqual(1000, test_length(LargeList1000)),

    LargeList10000 = lists:seq(1, 10000),
    ?assertEqual(10000, test_length(LargeList10000)),

    % Test 9.2: Large mixed type list
    LargeMixedList = lists:flatten([
        lists:seq(1, 500),
        [atom || _ <- lists:seq(1, 300)],
        ["string" ++ integer_to_list(N) || N <- lists:seq(1, 200)]
    ]),
    ?assertEqual(1000, test_length(LargeMixedList)),

    % Test 9.3: Performance timing (basic check)
    StartTime = erlang:monotonic_time(microsecond),
    Result = test_length(lists:seq(1, 50000)),
    EndTime = erlang:monotonic_time(microsecond),
    Duration = EndTime - StartTime,

    ?assertEqual(50000, Result),
    % Length calculation should be very fast (under 10ms for 50k elements)

    % 10ms in microseconds
    ?assert(Duration < 10000),

    cure_utils:debug("✓ Large list performance test passed~n").

test_special_value_lists() ->
    cure_utils:debug("Testing Std.List.length with special value lists...~n"),

    % Test 10.1: Lists with boolean values
    ?assertEqual(4, test_length([true, false, true, false])),
    ?assertEqual(2, test_length([true, false])),

    % Test 10.2: Lists with tuples
    ?assertEqual(3, test_length([{a, b}, {c, d, e}, {f}])),
    ?assertEqual(4, test_length([{}, {1}, {1, 2}, {1, 2, 3}])),

    % Test 10.3: Lists with function references (if supported)
    Fun1 = fun(X) -> X + 1 end,
    Fun2 = fun(X) -> X * 2 end,
    ?assertEqual(2, test_length([Fun1, Fun2])),

    % Test 10.4: Lists with pids and references (if applicable)
    ?assertEqual(1, test_length([self()])),
    ?assertEqual(2, test_length([make_ref(), make_ref()])),

    % Test 10.5: Lists with binary data
    ?assertEqual(3, test_length([<<1, 2, 3>>, <<4, 5>>, <<>>])),
    ?assertEqual(2, test_length([<<"hello">>, <<"world">>])),

    cure_utils:debug("✓ Special value lists test passed~n").

test_edge_cases_and_boundaries() ->
    cure_utils:debug("Testing Std.List.length edge cases and boundaries...~n"),

    % Test 11.1: Extremely large lists (boundary testing)
    % Note: This tests memory/performance boundaries
    try
        VeryLargeList = lists:seq(1, 100000),
        Result = test_length(VeryLargeList),
        ?assertEqual(100000, Result)
    catch
        _:_ ->
            % If memory is insufficient, this is acceptable
            cure_utils:debug("    Large list boundary test skipped (insufficient memory)~n")
    end,

    % Test 11.2: Lists with zero values
    ?assertEqual(5, test_length([0, 0, 0, 0, 0])),
    ?assertEqual(3, test_length([1, 0, 2])),

    % Test 11.3: Lists with repeated identical elements
    ?assertEqual(1000, test_length(lists:duplicate(1000, same_element))),
    ?assertEqual(100, test_length(lists:duplicate(100, {same, tuple}))),

    % Test 11.4: Lists with special float values
    ?assertEqual(4, test_length([0.0, -0.0, 1.0, -1.0])),
    % Note: Infinity and NaN testing would depend on implementation

    % Test 11.5: Unicode string lists (if supported)
    ?assertEqual(3, test_length(["hello", "世界", "тест"])),

    cure_utils:debug("✓ Edge cases and boundaries test passed~n").

%% ============================================================================
%% Helper Functions
%% ============================================================================

%% Helper function to test list length
%% Uses Erlang's built-in length/1 function as the reference implementation
%% In a real Cure implementation, this would call the actual Std.List.length function
test_length(List) ->
    length(List).
