#!/bin/bash

# Cure Standard Library Loading Tests Runner
# Compiles and runs the stdlib loading unit tests

set -e  # Exit on error

CURE_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$CURE_ROOT"

echo "=================================================================================="
echo " CURE STANDARD LIBRARY LOADING TESTS"
echo "=================================================================================="
echo

# Ensure the project is built
echo "Building Cure compiler and standard library..."
make clean && make all
echo

# Compile the test file
echo "Compiling stdlib loading tests..."
erlc -I src -pa _build/ebin -o _build/ebin test/stdlib_loading_test.erl

# Run the tests
echo "Running stdlib loading tests..."
echo

erl -pa _build/ebin -s stdlib_loading_test run -s init stop

echo
echo "=================================================================================="
echo " TESTS COMPLETED SUCCESSFULLY"
echo "=================================================================================="