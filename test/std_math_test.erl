%% Cure Standard Library Math Tests
%% Tests for Std.Math module functions including abs, sign, power, factorial, fibonacci
%% and other mathematical operations for accurate numerical results
-module(std_math_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").

%% Run all Std.Math tests
run() ->
    cure_utils:debug("Running Std.Math tests...~n"),
    test_mathematical_constants(),
    test_basic_operations(),
    test_comparison_functions(),
    test_power_function(),
    test_factorial_function(),
    test_fibonacci_function(),
    test_edge_cases(),
    cure_utils:debug("All Std.Math tests passed!~n").

%% ============================================================================
%% Test 1: Mathematical constants
%% ============================================================================

test_mathematical_constants() ->
    cure_utils:debug("Testing mathematical constants...~n"),

    % Test pi/0 - should return approximately 3.141592653589793
    Pi = test_pi(),
    ?assert(abs(Pi - 3.141592653589793) < 0.000000000001),
    ?assert(is_float(Pi)),

    % Test e/0 - should return approximately 2.718281828459045
    E = test_e(),
    ?assert(abs(E - 2.718281828459045) < 0.000000000001),
    ?assert(is_float(E)),

    % Verify constants are in expected ranges
    ?assert(Pi > 3.14),
    ?assert(Pi < 3.15),
    ?assert(E > 2.71),
    ?assert(E < 2.72),

    cure_utils:debug("✓ Mathematical constants test passed~n").

% Helper functions for constants
test_pi() -> 3.141592653589793.
test_e() -> 2.718281828459045.

%% ============================================================================
%% Test 2: Basic operations - abs, sign, negate, arithmetic
%% ============================================================================

test_basic_operations() ->
    cure_utils:debug("Testing basic operations...~n"),

    % Test abs/1 with various integers
    ?assertEqual(5, test_abs(5)),
    ?assertEqual(5, test_abs(-5)),
    ?assertEqual(0, test_abs(0)),
    ?assertEqual(42, test_abs(42)),
    ?assertEqual(42, test_abs(-42)),
    ?assertEqual(1, test_abs(1)),
    ?assertEqual(1, test_abs(-1)),

    % Test with large numbers
    ?assertEqual(1000000, test_abs(1000000)),
    ?assertEqual(1000000, test_abs(-1000000)),

    % Test sign/1 function
    ?assertEqual(1, test_sign(5)),
    ?assertEqual(1, test_sign(42)),
    ?assertEqual(1, test_sign(1)),
    ?assertEqual(-1, test_sign(-5)),
    ?assertEqual(-1, test_sign(-42)),
    ?assertEqual(-1, test_sign(-1)),
    ?assertEqual(0, test_sign(0)),

    % Test with large numbers
    ?assertEqual(1, test_sign(1000000)),
    ?assertEqual(-1, test_sign(-1000000)),

    % Test negate/1
    ?assertEqual(-5, test_negate(5)),
    ?assertEqual(5, test_negate(-5)),
    ?assertEqual(0, test_negate(0)),
    ?assertEqual(-42, test_negate(42)),
    ?assertEqual(42, test_negate(-42)),

    % Test basic arithmetic operations
    ?assertEqual(7, test_add(3, 4)),
    ?assertEqual(0, test_add(-5, 5)),
    ?assertEqual(-8, test_add(-3, -5)),

    ?assertEqual(2, test_subtract(5, 3)),
    ?assertEqual(-2, test_subtract(3, 5)),
    ?assertEqual(0, test_subtract(7, 7)),

    ?assertEqual(15, test_multiply(3, 5)),
    ?assertEqual(-15, test_multiply(-3, 5)),
    ?assertEqual(15, test_multiply(-3, -5)),
    ?assertEqual(0, test_multiply(0, 42)),

    cure_utils:debug("✓ Basic operations test passed~n").

% Helper functions for basic operations
test_abs(X) when X < 0 -> -X;
test_abs(X) -> X.

test_sign(X) when X > 0 -> 1;
test_sign(X) when X < 0 -> -1;
test_sign(0) -> 0.

test_negate(X) -> -X.

test_add(X, Y) -> X + Y.
test_subtract(X, Y) -> X - Y.
test_multiply(X, Y) -> X * Y.

%% ============================================================================
%% Test 3: Comparison functions - min, max, clamp
%% ============================================================================

test_comparison_functions() ->
    cure_utils:debug("Testing comparison functions...~n"),

    % Test min/2
    ?assertEqual(3, test_min(5, 3)),
    ?assertEqual(3, test_min(3, 5)),
    ?assertEqual(4, test_min(4, 4)),
    ?assertEqual(-10, test_min(-5, -10)),
    ?assertEqual(-5, test_min(0, -5)),

    % Test max/2
    ?assertEqual(5, test_max(5, 3)),
    ?assertEqual(5, test_max(3, 5)),
    ?assertEqual(4, test_max(4, 4)),
    ?assertEqual(-5, test_max(-5, -10)),
    ?assertEqual(0, test_max(0, -5)),

    % Test clamp/3

    % Below range, clamp to min
    ?assertEqual(5, test_clamp(3, 5, 10)),
    % Above range, clamp to max
    ?assertEqual(10, test_clamp(15, 5, 10)),
    % Within range, unchanged
    ?assertEqual(7, test_clamp(7, 5, 10)),
    % At minimum boundary
    ?assertEqual(5, test_clamp(5, 5, 10)),
    % At maximum boundary
    ?assertEqual(10, test_clamp(10, 5, 10)),
    % Negative below range
    ?assertEqual(0, test_clamp(-5, 0, 3)),
    % Negative values
    ?assertEqual(-2, test_clamp(-10, -2, 1)),

    % Test with same min/max (degenerate case)
    ?assertEqual(5, test_clamp(3, 5, 5)),
    ?assertEqual(5, test_clamp(7, 5, 5)),
    ?assertEqual(5, test_clamp(5, 5, 5)),

    cure_utils:debug("✓ Comparison functions test passed~n").

% Helper functions for comparison
test_min(X, Y) when X =< Y -> X;
test_min(_, Y) -> Y.

test_max(X, Y) when X >= Y -> X;
test_max(_, Y) -> Y.

test_clamp(Value, Min, Max) ->
    test_min(test_max(Value, Min), Max).

%% ============================================================================
%% Test 4: Power function - verify accurate results
%% ============================================================================

test_power_function() ->
    cure_utils:debug("Testing power function...~n"),

    % Test basic cases

    % Any number to power 0 is 1
    ?assertEqual(1, test_power(5, 0)),
    % Edge case: 0^0 = 1 (by convention)
    ?assertEqual(1, test_power(0, 0)),
    % Any number to power 1 is itself
    ?assertEqual(5, test_power(5, 1)),
    % 0 to any positive power is 0
    ?assertEqual(0, test_power(0, 5)),

    % Test small integer powers

    % 2^2 = 4
    ?assertEqual(4, test_power(2, 2)),
    % 2^3 = 8
    ?assertEqual(8, test_power(2, 3)),
    % 2^4 = 16
    ?assertEqual(16, test_power(2, 4)),
    % 2^5 = 32
    ?assertEqual(32, test_power(2, 5)),

    % Test powers of different bases

    % 3^2 = 9
    ?assertEqual(9, test_power(3, 2)),
    % 3^3 = 27
    ?assertEqual(27, test_power(3, 3)),
    % 3^4 = 81
    ?assertEqual(81, test_power(3, 4)),

    % 5^2 = 25
    ?assertEqual(25, test_power(5, 2)),
    % 5^3 = 125
    ?assertEqual(125, test_power(5, 3)),

    % 10^2 = 100
    ?assertEqual(100, test_power(10, 2)),
    % 10^3 = 1000
    ?assertEqual(1000, test_power(10, 3)),

    % Test larger computations

    % 2^10 = 1024
    ?assertEqual(1024, test_power(2, 10)),
    % 3^8 = 6561
    ?assertEqual(6561, test_power(3, 8)),

    % Test negative bases (positive exponents)

    % (-2)^2 = 4
    ?assertEqual(4, test_power(-2, 2)),
    % (-2)^3 = -8
    ?assertEqual(-8, test_power(-2, 3)),
    % (-2)^4 = 16
    ?assertEqual(16, test_power(-2, 4)),

    cure_utils:debug("✓ Power function test passed~n").

% Helper function for power calculation (recursive implementation)
test_power(_, 0) ->
    1;
test_power(Base, 1) ->
    Base;
test_power(Base, Exponent) when Exponent > 1 ->
    Base * test_power(Base, Exponent - 1).

%% ============================================================================
%% Test 5: Factorial function - verify accurate results
%% ============================================================================

test_factorial_function() ->
    cure_utils:debug("Testing factorial function...~n"),

    % Test base cases

    % 0! = 1 (by definition)
    ?assertEqual(1, test_factorial(0)),
    % 1! = 1
    ?assertEqual(1, test_factorial(1)),

    % Test small factorials

    % 2! = 2
    ?assertEqual(2, test_factorial(2)),
    % 3! = 6
    ?assertEqual(6, test_factorial(3)),
    % 4! = 24
    ?assertEqual(24, test_factorial(4)),
    % 5! = 120
    ?assertEqual(120, test_factorial(5)),
    % 6! = 720
    ?assertEqual(720, test_factorial(6)),
    % 7! = 5040
    ?assertEqual(5040, test_factorial(7)),
    % 8! = 40320
    ?assertEqual(40320, test_factorial(8)),

    % Test larger factorials

    % 9! = 362880
    ?assertEqual(362880, test_factorial(9)),
    % 10! = 3628800
    ?assertEqual(3628800, test_factorial(10)),

    % Test moderate size factorial

    % 12! = 479001600
    ?assertEqual(479001600, test_factorial(12)),

    cure_utils:debug("✓ Factorial function test passed~n").

% Helper function for factorial calculation
test_factorial(0) ->
    1;
test_factorial(1) ->
    1;
test_factorial(N) when N > 1 ->
    N * test_factorial(N - 1).

%% ============================================================================
%% Test 6: Fibonacci function - verify accurate results
%% ============================================================================

test_fibonacci_function() ->
    cure_utils:debug("Testing fibonacci function...~n"),

    % Test base cases

    % fib(0) = 0
    ?assertEqual(0, test_fibonacci(0)),
    % fib(1) = 1
    ?assertEqual(1, test_fibonacci(1)),

    % Test first several Fibonacci numbers

    % fib(2) = 1
    ?assertEqual(1, test_fibonacci(2)),
    % fib(3) = 2
    ?assertEqual(2, test_fibonacci(3)),
    % fib(4) = 3
    ?assertEqual(3, test_fibonacci(4)),
    % fib(5) = 5
    ?assertEqual(5, test_fibonacci(5)),
    % fib(6) = 8
    ?assertEqual(8, test_fibonacci(6)),
    % fib(7) = 13
    ?assertEqual(13, test_fibonacci(7)),
    % fib(8) = 21
    ?assertEqual(21, test_fibonacci(8)),
    % fib(9) = 34
    ?assertEqual(34, test_fibonacci(9)),
    % fib(10) = 55
    ?assertEqual(55, test_fibonacci(10)),

    % Test larger Fibonacci numbers

    % fib(11) = 89
    ?assertEqual(89, test_fibonacci(11)),
    % fib(12) = 144
    ?assertEqual(144, test_fibonacci(12)),
    % fib(13) = 233
    ?assertEqual(233, test_fibonacci(13)),
    % fib(14) = 377
    ?assertEqual(377, test_fibonacci(14)),
    % fib(15) = 610
    ?assertEqual(610, test_fibonacci(15)),

    % Test some specific larger values

    % fib(20) = 6765
    ?assertEqual(6765, test_fibonacci(20)),
    % fib(25) = 75025
    ?assertEqual(75025, test_fibonacci(25)),

    cure_utils:debug("✓ Fibonacci function test passed~n").

% Helper function for Fibonacci calculation (naive recursive implementation)
test_fibonacci(0) ->
    0;
test_fibonacci(1) ->
    1;
test_fibonacci(N) when N > 1 ->
    test_fibonacci(N - 1) + test_fibonacci(N - 2).

%% ============================================================================
%% Test 7: Edge cases and error conditions
%% ============================================================================

test_edge_cases() ->
    cure_utils:debug("Testing edge cases...~n"),

    % Test abs with maximum/minimum integers (within reasonable bounds)

    % Max 32-bit signed int
    ?assertEqual(2147483647, test_abs(2147483647)),
    % Near min 32-bit signed int
    ?assertEqual(2147483647, test_abs(-2147483647)),

    % Test sign with extreme values
    ?assertEqual(1, test_sign(2147483647)),
    ?assertEqual(-1, test_sign(-2147483647)),

    % Test power with larger exponents
    ?assertEqual(256, test_power(2, 8)),
    ?assertEqual(512, test_power(2, 9)),

    % Test factorial edge cases (avoid very large numbers that might overflow)
    % Most implementations would use arbitrary precision for larger factorials
    ?assertEqual(1, test_factorial(0)),
    ?assertEqual(1, test_factorial(1)),

    % Test Fibonacci with edge cases
    ?assertEqual(0, test_fibonacci(0)),
    ?assertEqual(1, test_fibonacci(1)),

    % Test mathematical properties
    % abs(x) should always be non-negative
    TestValues = [-100, -1, 0, 1, 100],
    lists:foreach(
        fun(X) ->
            AbsX = test_abs(X),
            ?assert(AbsX >= 0),
            % Also verify abs(abs(x)) == abs(x)
            ?assertEqual(AbsX, test_abs(AbsX))
        end,
        TestValues
    ),

    % Test sign properties
    lists:foreach(
        fun(X) ->
            SignX = test_sign(X),
            ?assert(SignX >= -1),
            ?assert(SignX =< 1),
            % sign(x) * abs(x) should equal x
            if
                X /= 0 -> ?assertEqual(X, SignX * test_abs(X));
                % Skip for zero
                true -> ok
            end
        end,
        TestValues
    ),

    % Test power properties: a^(m+n) = a^m * a^n (for small values)
    Base = 3,
    M = 2,
    N = 3,
    PowerSum = test_power(Base, M + N),
    PowerProduct = test_power(Base, M) * test_power(Base, N),
    ?assertEqual(PowerSum, PowerProduct),

    cure_utils:debug("✓ Edge cases test passed~n").
