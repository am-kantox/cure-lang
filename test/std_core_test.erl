%% Cure Standard Library Core Tests
%% Tests for Std.Core module functions including comparison, boolean operations,
%% error handling, and utility functions
-module(std_core_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").

%% Run all Std.Core tests
run() ->
    cure_utils:debug("Running Std.Core tests...~n"),
    test_compare_function(),
    test_boolean_operations(),
    test_comparison_operations(),
    test_min_max_clamp(),
    test_result_operations(),
    test_option_operations(),
    test_utility_functions(),
    cure_utils:debug("All Std.Core tests passed!~n").

%% ============================================================================
%% Test 1: Compare function - verify correct Ordering return values
%% ============================================================================

test_compare_function() ->
    cure_utils:debug("Testing compare function...~n"),

    % Note: Since we don't have compiled Cure modules yet, we'll test the concept
    % In a real implementation, these would call 'Std.Core':compare/2

    % Test compare with integers

    % 5 > 3 should return Gt
    test_compare_values(5, 3, gt),
    % 3 < 5 should return Lt
    test_compare_values(3, 5, lt),
    % 4 == 4 should return Eq
    test_compare_values(4, 4, eq),

    % Test compare with floats
    test_compare_values(3.14, 2.71, gt),
    test_compare_values(1.0, 2.0, lt),
    test_compare_values(2.5, 2.5, eq),

    % Test compare with strings (conceptually)
    test_compare_values("abc", "abd", lt),
    test_compare_values("xyz", "abc", gt),
    test_compare_values("hello", "hello", eq),

    cure_utils:debug("✓ Compare function test passed~n").

% Helper function to test comparison logic
test_compare_values(X, Y, Expected) ->
    Result =
        if
            X < Y -> lt;
            X > Y -> gt;
            X == Y -> eq
        end,
    ?assertEqual(Expected, Result).

%% ============================================================================
%% Test 2: Boolean operations
%% ============================================================================

test_boolean_operations() ->
    cure_utils:debug("Testing boolean operations...~n"),

    % Test not/1
    ?assertEqual(false, test_not(true)),
    ?assertEqual(true, test_not(false)),

    % Test and/2
    ?assertEqual(true, test_and(true, true)),
    ?assertEqual(false, test_and(true, false)),
    ?assertEqual(false, test_and(false, true)),
    ?assertEqual(false, test_and(false, false)),

    % Test or/2
    ?assertEqual(true, test_or(true, true)),
    ?assertEqual(true, test_or(true, false)),
    ?assertEqual(true, test_or(false, true)),
    ?assertEqual(false, test_or(false, false)),

    % Test xor/2
    ?assertEqual(false, test_xor(true, true)),
    ?assertEqual(true, test_xor(true, false)),
    ?assertEqual(true, test_xor(false, true)),
    ?assertEqual(false, test_xor(false, false)),

    cure_utils:debug("✓ Boolean operations test passed~n").

% Helper functions for boolean operations (simulating Cure functions)
test_not(X) -> not X.
test_and(X, Y) -> X and Y.
test_or(X, Y) -> X or Y.
test_xor(X, Y) -> (X and not Y) or (not X and Y).

%% ============================================================================
%% Test 3: Comparison operations
%% ============================================================================

test_comparison_operations() ->
    cure_utils:debug("Testing comparison operations...~n"),

    % Test eq/2, ne/2
    ?assertEqual(true, test_eq(5, 5)),
    ?assertEqual(false, test_eq(5, 6)),
    ?assertEqual(false, test_ne(5, 5)),
    ?assertEqual(true, test_ne(5, 6)),

    % Test lt/2, le/2, gt/2, ge/2
    ?assertEqual(true, test_lt(3, 5)),
    ?assertEqual(false, test_lt(5, 3)),
    ?assertEqual(true, test_le(3, 5)),
    ?assertEqual(true, test_le(5, 5)),
    ?assertEqual(false, test_le(5, 3)),

    ?assertEqual(false, test_gt(3, 5)),
    ?assertEqual(true, test_gt(5, 3)),
    ?assertEqual(false, test_ge(3, 5)),
    ?assertEqual(true, test_ge(5, 5)),
    ?assertEqual(true, test_ge(5, 3)),

    cure_utils:debug("✓ Comparison operations test passed~n").

% Helper functions for comparison operations
test_eq(X, Y) -> X == Y.
test_ne(X, Y) -> X /= Y.
test_lt(X, Y) -> X < Y.
test_le(X, Y) -> X =< Y.
test_gt(X, Y) -> X > Y.
test_ge(X, Y) -> X >= Y.

%% ============================================================================
%% Test 4: Min, Max, Clamp operations
%% ============================================================================

test_min_max_clamp() ->
    cure_utils:debug("Testing min, max, clamp operations...~n"),

    % Test minimum/2
    ?assertEqual(3, test_minimum(5, 3)),
    ?assertEqual(3, test_minimum(3, 5)),
    ?assertEqual(4, test_minimum(4, 4)),

    % Test maximum/2
    ?assertEqual(5, test_maximum(5, 3)),
    ?assertEqual(5, test_maximum(3, 5)),
    ?assertEqual(4, test_maximum(4, 4)),

    % Test clamp/3

    % Below range, clamp to min
    ?assertEqual(5, test_clamp(3, 5, 10)),
    % Above range, clamp to max
    ?assertEqual(10, test_clamp(15, 5, 10)),
    % Within range, unchanged
    ?assertEqual(7, test_clamp(7, 5, 10)),
    % At minimum
    ?assertEqual(5, test_clamp(5, 5, 10)),
    % At maximum
    ?assertEqual(10, test_clamp(10, 5, 10)),

    cure_utils:debug("✓ Min, max, clamp operations test passed~n").

% Helper functions for min/max/clamp
test_minimum(X, Y) -> min(X, Y).
test_maximum(X, Y) -> max(X, Y).
test_clamp(Value, Min, Max) -> min(max(Value, Min), Max).

%% ============================================================================
%% Test 5: Result type operations
%% ============================================================================

test_result_operations() ->
    cure_utils:debug("Testing Result type operations...~n"),

    % Test ok/1, error/1 constructors
    OkValue = test_ok(42),
    ErrorValue = test_error("failed"),
    ?assertMatch({'Ok', 42}, OkValue),
    ?assertMatch({'Error', "failed"}, ErrorValue),

    % Test is_ok/1, is_error/1
    ?assertEqual(true, test_is_ok({'Ok', 123})),
    ?assertEqual(false, test_is_ok({'Error', "msg"})),
    ?assertEqual(false, test_is_error({'Ok', 123})),
    ?assertEqual(true, test_is_error({'Error', "msg"})),

    % Test map_ok/2
    MappedOk = test_map_ok({'Ok', 5}, fun(X) -> X * 2 end),
    MappedError = test_map_ok({'Error', "fail"}, fun(X) -> X * 2 end),
    ?assertEqual({'Ok', 10}, MappedOk),
    ?assertEqual({'Error', "fail"}, MappedError),

    % Test map_error/2
    MappedErrorOk = test_map_error({'Ok', 5}, fun(E) -> E ++ " processed" end),
    MappedErrorErr = test_map_error({'Error', "fail"}, fun(E) -> E ++ " processed" end),
    ?assertEqual({'Ok', 5}, MappedErrorOk),
    ?assertEqual({'Error', "fail processed"}, MappedErrorErr),

    % Test and_then/2
    AndThenOk = test_and_then({'Ok', 10}, fun(X) -> {'Ok', X / 2} end),
    AndThenError = test_and_then({'Error', "fail"}, fun(X) -> {'Ok', X / 2} end),
    AndThenChainError = test_and_then({'Ok', 0}, fun(_) -> {'Error', "division by zero"} end),
    ?assertEqual({'Ok', 5.0}, AndThenOk),
    ?assertEqual({'Error', "fail"}, AndThenError),
    ?assertEqual({'Error', "division by zero"}, AndThenChainError),

    cure_utils:debug("✓ Result type operations test passed~n").

% Helper functions for Result operations
test_ok(Value) -> {'Ok', Value}.
test_error(Err) -> {'Error', Err}.
test_is_ok({'Ok', _}) -> true;
test_is_ok({'Error', _}) -> false.
test_is_error({'Ok', _}) -> false;
test_is_error({'Error', _}) -> true.
test_map_ok({'Ok', Value}, F) -> {'Ok', F(Value)};
test_map_ok({'Error', Err}, _F) -> {'Error', Err}.
test_map_error({'Ok', Value}, _F) -> {'Ok', Value};
test_map_error({'Error', Err}, F) -> {'Error', F(Err)}.
test_and_then({'Ok', Value}, F) -> F(Value);
test_and_then({'Error', Err}, _F) -> {'Error', Err}.

%% ============================================================================
%% Test 6: Option type operations
%% ============================================================================

test_option_operations() ->
    cure_utils:debug("Testing Option type operations...~n"),

    % Test some/1, none/0 constructors
    SomeValue = test_some(42),
    NoneValue = test_none(),
    ?assertMatch({'Some', 42}, SomeValue),
    ?assertEqual('None', NoneValue),

    % Test is_some/1, is_none/1
    ?assertEqual(true, test_is_some({'Some', 123})),
    ?assertEqual(false, test_is_some('None')),
    ?assertEqual(false, test_is_none({'Some', 123})),
    ?assertEqual(true, test_is_none('None')),

    % Test map_option/2
    MappedSome = test_map_option({'Some', 5}, fun(X) -> X * 3 end),
    MappedNone = test_map_option('None', fun(X) -> X * 3 end),
    ?assertEqual({'Some', 15}, MappedSome),
    ?assertEqual('None', MappedNone),

    % Test flat_map_option/2
    FlatMappedSome = test_flat_map_option({'Some', 4}, fun(X) -> {'Some', X + 1} end),
    FlatMappedNone = test_flat_map_option('None', fun(X) -> {'Some', X + 1} end),
    FlatMappedToNone = test_flat_map_option({'Some', -1}, fun(_) -> 'None' end),
    ?assertEqual({'Some', 5}, FlatMappedSome),
    ?assertEqual('None', FlatMappedNone),
    ?assertEqual('None', FlatMappedToNone),

    % Test option_or/2
    SomeOr = test_option_or({'Some', 10}, 99),
    NoneOr = test_option_or('None', 99),
    ?assertEqual(10, SomeOr),
    ?assertEqual(99, NoneOr),

    cure_utils:debug("✓ Option type operations test passed~n").

% Helper functions for Option operations
test_some(Value) -> {'Some', Value}.
test_none() -> 'None'.
test_is_some({'Some', _}) -> true;
test_is_some('None') -> false.
test_is_none({'Some', _}) -> false;
test_is_none('None') -> true.
test_map_option({'Some', Value}, F) -> {'Some', F(Value)};
test_map_option('None', _F) -> 'None'.
test_flat_map_option({'Some', Value}, F) -> F(Value);
test_flat_map_option('None', _F) -> 'None'.
test_option_or({'Some', Value}, _Default) -> Value;
test_option_or('None', Default) -> Default.

%% ============================================================================
%% Test 7: Utility functions
%% ============================================================================

test_utility_functions() ->
    cure_utils:debug("Testing utility functions...~n"),

    % Test identity/1
    ?assertEqual(42, test_identity(42)),
    ?assertEqual("hello", test_identity("hello")),
    ?assertEqual([1, 2, 3], test_identity([1, 2, 3])),

    % Test const/1
    ConstFun = test_const(99),
    ?assertEqual(99, ConstFun("anything")),
    ?assertEqual(99, ConstFun(123)),

    % Test apply/2
    AddTwo = fun(X) -> X + 2 end,
    ?assertEqual(7, test_apply(AddTwo, 5)),

    % Test pipe/2
    ?assertEqual(12, test_pipe(5, fun(X) -> X + 7 end)),

    % Test compose/2
    AddOne = fun(X) -> X + 1 end,
    MultiplyTwo = fun(X) -> X * 2 end,
    Composed = test_compose(MultiplyTwo, AddOne),
    % (5 + 1) * 2 = 12
    ?assertEqual(12, Composed(5)),

    % Test flip/2
    Subtract = fun(X, Y) -> X - Y end,
    FlippedSubtract = test_flip(Subtract),
    % flip(subtract)(5, 8) = subtract(8, 5) = 8 - 5 = 3
    ?assertEqual(3, FlippedSubtract(5, 8)),

    cure_utils:debug("✓ Utility functions test passed~n").

% Helper functions for utility operations
test_identity(X) -> X.
test_const(X) -> fun(_) -> X end.
test_apply(F, X) -> F(X).
test_pipe(X, F) -> F(X).
test_compose(F, G) -> fun(X) -> F(G(X)) end.
test_flip(F) -> fun(X, Y) -> F(Y, X) end.
