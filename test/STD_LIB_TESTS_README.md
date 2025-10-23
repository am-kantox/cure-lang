# Cure Standard Library Unit Tests

This directory contains comprehensive unit tests for the Cure programming language standard library modules.

## Test Coverage

The test suite covers five main standard library modules:

### 1. **Std.Core** (`std_core_test.erl`)
Tests core functionality including:
- **compare/2** - Returns correct Ordering values (Lt, Eq, Gt) for different input types
- **Boolean operations** - not/1, and/2, or/2, xor/2
- **Comparison operations** - eq/2, ne/2, lt/2, le/2, gt/2, ge/2
- **Min/max operations** - minimum/2, maximum/2, clamp/3
- **Result type operations** - ok/1, error/1, map_ok/2, and_then/2
- **Option type operations** - some/1, none/0, map_option/2, flat_map_option/2
- **Utility functions** - identity/1, compose/2, flip/1, const/1, apply/2, pipe/2

### 2. **Std.IO** (`std_io_test.erl`)
Tests input/output operations:
- **Print functions** - Verifies that print/1 and println/1 return Int (0) instead of Unit
- **Type-specific printing** - print_int/1, print_float/1, print_bool/1
- **Input operations** - read_line/0, read_int/0, read_float/0 (placeholder implementations)
- **Debug/error output** - debug/1, error/1

### 3. **Std.List** (`std_list_test.erl`)
Tests list operations and transformations:
- **Basic operations** - length/1, head/1, tail/1, is_empty/1
- **Construction** - cons/2, append/2, reverse/1
- **Transformation** - map/2, filter/2, fold_left/3, fold_right/3
- **Access** - nth/2, take/2, drop/2
- **Predicates** - all/2, any/2, contains/2
- **Safe operations** - safe_head/1, safe_tail/1, safe_nth/2

### 4. **Std.Math** (`std_math_test.erl`)
Tests mathematical operations for numerical accuracy:
- **Constants** - pi/0, e/0
- **Basic operations** - abs/1, sign/1, negate/1
- **Arithmetic** - add/2, subtract/2, multiply/2
- **Comparison** - min/2, max/2, clamp/3
- **Advanced functions** - power/2, factorial/1, fibonacci/1
- **Edge cases** - Large numbers, mathematical properties validation

### 5. **Std.String** (`std_string_test.erl`)
Tests string operations (many with placeholder implementations):
- **Basic operations** - length/1, is_empty/1
- **Construction** - concat/2, repeat/2
- **Conversion** - to_upper/1, to_lower/1 (placeholders)
- **Predicates** - starts_with/2, ends_with/2 (placeholders)
- **Manipulation** - trim/1, reverse/1 (placeholders)
- **Access** - slice/3, take/2, drop/2 (placeholders)

## Running the Tests

### Prerequisites

```bash
# Compile the test modules
erlc -o _build/ebin test/std_*_test.erl
```

### Running Individual Test Modules

```bash
# Run Std.Core tests
erl -pa _build/ebin -s std_core_test run -s init stop

# Run Std.IO tests
erl -pa _build/ebin -s std_io_test run -s init stop

# Run Std.List tests
erl -pa _build/ebin -s std_list_test run -s init stop

# Run Std.Math tests
erl -pa _build/ebin -s std_math_test run -s init stop

# Run Std.String tests
erl -pa _build/ebin -s std_string_test run -s init stop
```

### Using the Comprehensive Test Runner

The comprehensive test runner (`std_comprehensive_test.erl`) provides several ways to run tests:

```bash
# Run all standard library tests
erl -pa _build/ebin -s std_comprehensive_test run -s init stop

# Run tests with detailed timing information
erl -pa _build/ebin -s std_comprehensive_test run_with_timing -s init stop

# Run an individual test module via the comprehensive runner
erl -pa _build/ebin -eval "std_comprehensive_test:run_individual(std_core_test)." -s init stop
```

## Test Implementation Notes

### Design Principles

1. **Current State Testing**: Tests validate both current behavior (including placeholders) and expected future behavior
2. **Erlang Simulation**: All tests use Erlang implementations to simulate Cure function behavior
3. **Comprehensive Coverage**: Each function is tested with multiple inputs, edge cases, and error conditions
4. **Clear Documentation**: Each test includes comments explaining what it's testing and why

### Placeholder Implementations

Several Cure standard library functions currently have placeholder implementations:

- **Std.String functions** often return unchanged input or simplified values
- **Std.IO functions** return placeholder values (0 for Int returns, "" for String returns)
- Tests validate these current behaviors while documenting expected future behavior

### Integration with Cure Compiler

These tests are designed to require minimal changes when the actual Cure standard library is compiled:

1. **Function signatures** match the Cure specifications
2. **Test logic** is independent of implementation details
3. **Expected behaviors** are clearly documented
4. **Placeholder behaviors** are explicitly noted

### Test Structure

Each test module follows a consistent structure:

```erlang
%% Module exports and includes
-module(test_module).
-export([run/0]).
-include_lib("eunit/include/eunit.hrl").

%% Main test runner
run() ->
    test_function_group_1(),
    test_function_group_2(),
    % ... more test groups
    cure_utils:debug("All tests passed!~n").

%% Individual test functions
test_function_group_1() ->
    % Test cases with assertions
    ?assertEqual(expected, actual),
    % ...
    cure_utils:debug("✓ Test group 1 passed~n").

% Helper functions that simulate Cure standard library behavior
```

## Example Test Results

When all tests pass, you should see output like:

```
Running Std.Core tests...
Testing compare function...
✓ Compare function test passed
Testing boolean operations...
✓ Boolean operations test passed
...
All Std.Core tests passed!
```

## Contributing

When adding new tests:

1. Follow the existing naming conventions
2. Include both positive and negative test cases
3. Test edge cases and boundary conditions
4. Document any placeholder behavior
5. Ensure tests work with current implementations
6. Add comprehensive comments explaining test logic

## Future Development

As the Cure standard library evolves:

1. Update placeholder function implementations
2. Add tests for new standard library functions
3. Modify tests to match actual Cure compiler output
4. Extend edge case coverage
5. Add performance tests for critical functions

The test suite is designed to grow with the Cure language while maintaining backwards compatibility and clear documentation of expected behaviors.