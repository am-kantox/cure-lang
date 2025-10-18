# Standard Library Loading Unit Tests

## Overview

This test suite (`stdlib_loading_test.erl`) provides comprehensive unit tests for the standard library loading functionality in the Cure compiler's type checker. The tests verify that `.cure` standard library files can be dynamically loaded, parsed, and their function types correctly extracted and made available to the type system.

## Test Coverage

### 1. `load_stdlib_modules/0` Test

**Purpose**: Verifies that all `.cure` files in the standard library directory are successfully loaded and parsed.

**Key Validations**:
- Returns a non-empty map of function definitions
- Successfully loads functions from major stdlib modules (Std.Core, Std.List, Std.Math, etc.)
- Handles parsing errors gracefully (e.g., fsm.cure parsing issues)
- Function types are properly structured as `{function_type, ParamTypes, ReturnType}` tuples

**Expected Modules Tested**:
- `Std.Core`: Core functions like `identity`, `compose`, boolean operations
- `Std.List`: List operations like `length`, `head`, `map`, `filter`
- `Std.Math`: Mathematical operations like `pi`, `abs`, `power`
- `Std.IO`: I/O functions like `print`, `println`

### 2. `extract_module_functions/1` Test

**Purpose**: Verifies correct extraction of public function definitions from module ASTs.

**Key Validations**:
- Correctly extracts function name, arity, and type signature
- Only extracts public functions (excludes private functions marked with `is_private = true`)
- Handles both defined and undefined return types
- Works with empty AST inputs
- Returns functions keyed by `{ModuleName, FunctionName, Arity}` tuples

**Test Scenarios**:
- Public functions with explicit return types
- Public functions with inferred return types
- Private functions (should be excluded)
- Invalid/empty AST inputs

### 3. `add_std_function_types/1` Test

**Purpose**: Verifies that standard library functions are correctly added to the type environment.

**Key Validations**:
- Functions are accessible by their unqualified names in the environment
- Environment structure remains valid after stdlib integration
- Function types are correctly stored and retrievable
- Handles idempotent calls without errors
- Functions not in stdlib remain undefined

**Integration Points**:
- Uses `cure_types:lookup_env/2` to verify function availability
- Tests with functions from multiple stdlib modules
- Verifies environment record structure integrity

### 4. `get_stdlib_function_type/3` Test

**Purpose**: Verifies accurate type retrieval for standard library functions after dynamic loading.

**Key Validations**:
- Returns correct function types for valid stdlib functions
- Returns `not_found` for non-existent functions or modules
- Respects function arity in lookups
- Implements lazy loading and caching
- Handles invalid inputs gracefully

**Test Cases**:
- Valid function lookups from different modules
- Invalid function names and modules
- Incorrect arity specifications
- Caching verification through repeated calls

### 5. `create_function_type_from_signature/2` Test

**Purpose**: Verifies correct construction of function type tuples from parameter and return type definitions.

**Key Validations**:
- Handles defined return types correctly
- Creates type variables for undefined return types
- Processes various parameter type complexities
- Supports functions with no parameters
- Handles complex type expressions (lists, functions, etc.)

**Type Scenarios Tested**:
- Primitive types (Int, String, Bool, Float)
- Complex types (List types, Function types)
- Undefined return types (inferred as type variables)
- Zero-parameter functions

### 6. `create_function_type_from_signature_records/2` Test

**Purpose**: Verifies the record format version of function type creation handles both record and tuple parameter formats.

**Key Validations**:
- Works with `#param{}` record format
- Falls back to tuple format when needed
- Handles mixed parameter formats in the same function
- Maintains type correctness across format variations

## Integration and Workflow Tests

### Full Workflow Test

**Purpose**: Verifies the complete workflow from loading stdlib modules to making functions available in the type environment.

**Workflow Steps**:
1. Load stdlib modules from `.cure` files
2. Create base type environment
3. Integrate stdlib functions into environment
4. Verify function accessibility through environment lookups
5. Test direct type retrieval through the stdlib API

### Error Handling Test

**Purpose**: Verifies graceful handling of error conditions and invalid inputs.

**Error Scenarios**:
- Invalid AST structures
- Non-existent modules and functions
- Invalid function arities
- Empty or malformed inputs

## Technical Architecture

### Dependencies

The tests rely on several core Cure compiler modules:
- `cure_typechecker`: Main module being tested
- `cure_types`: Type system operations and environment management
- `cure_parser`: For parsing `.cure` source files
- `cure_ast_simple.hrl`: AST record definitions

### Type System Integration

The tests verify integration with Cure's type system:
- **Type Environment**: Uses `#type_env{}` records with bindings, constraints, and parent scopes
- **Function Types**: Validates `{function_type, [ParamTypes], ReturnType}` structures
- **Type Variables**: Tests creation and usage of type variables for inference

### File System Integration

Tests interact with the actual stdlib file system:
- Reads from `lib/std/` directory
- Handles file parsing errors gracefully
- Works with real `.cure` source files

## Running the Tests

### Manual Execution
```bash
cd /path/to/cure
make clean && make all
erlc -I src -pa _build/ebin -o _build/ebin test/stdlib_loading_test.erl
erl -pa _build/ebin -s stdlib_loading_test run -s init stop
```

### Using Test Runner
```bash
./test/run_stdlib_loading_tests.sh
```

## Expected Output

Successful test runs should show:
- Loading and parsing of 6+ stdlib modules
- Extraction of 70+ public functions
- All individual test cases passing
- Final confirmation message

## Known Limitations and Warnings

### Parsing Warnings
- `lib/std/fsm.cure`: Contains parsing errors due to grammar issues
- `lib/std/vector.cure`: Type checking failures due to unbound variables

These warnings are expected and don't affect the core functionality being tested.

### Test Environment
- Uses process dictionary for caching (`put`/`get` operations)
- Tests clean up state between individual test cases
- Requires full Cure compiler build to function properly

## Maintenance Notes

### Adding New Test Cases
1. Add test functions following the `test_*` naming pattern
2. Update the main `run/0` function to call new tests
3. Use EUnit assertions (`?assert`, `?assertEqual`, `?assertMatch`)
4. Follow existing pattern of setup, action, verification

### Updating for New Stdlib Functions
When new functions are added to the standard library:
1. Update expected function counts in `load_stdlib_modules/0` test
2. Add specific function checks in `get_stdlib_function_type/3` test
3. Verify functions appear in environment in `add_std_function_types/1` test

### Debugging Test Failures
- Check that `make all` completed successfully
- Verify stdlib files are present in `lib/std/`
- Ensure test file compiles without errors
- Check for changes in AST record definitions
- Verify export list in `cure_typechecker.erl` includes test functions

## Integration with CI/CD

These tests can be integrated into automated testing pipelines:
- Return appropriate exit codes (0 for success, non-zero for failure)
- Provide clear output for test results
- Can be run as part of broader test suites
- Compatible with standard Erlang testing frameworks