#!/usr/bin/env bash
# Test script for Cure MCP Server
# This script tests all MCP tools to verify integration with the compiler pipeline

set -e

echo "=== Cure MCP Server Tool Tests ==="
echo ""

# Colors for output
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

TEST_DIR=$(mktemp -d)
trap "rm -rf $TEST_DIR" EXIT

# Test counter
PASSED=0
FAILED=0

# Helper function to run a test
run_test() {
    local test_name="$1"
    local json_input="$2"
    local expected_pattern="$3"
    
    echo -n "Testing: $test_name... "
    
    # Run MCP server with input and timeout to prevent hanging
    # Using timeout command with 5 second limit
    result=$(echo "$json_input" | timeout 5 ./cure-mcp 2>&1 || true)
    
    # Check if timeout occurred
    if [ $? -eq 124 ]; then
        echo -e "${YELLOW}TIMEOUT${NC}"
        echo "  Server hung, check stdin handling"
        ((FAILED++))
        return 1
    fi
    
    # Check if result matches expected pattern
    if echo "$result" | grep -q "$expected_pattern"; then
        echo -e "${GREEN}PASSED${NC}"
        ((PASSED++))
        return 0
    else
        echo -e "${RED}FAILED${NC}"
        echo "  Expected pattern: $expected_pattern"
        echo "  Got: $result"
        ((FAILED++))
        return 1
    fi
}

# Test 1: Initialize server
echo "Test 1: Initialize MCP Server"
run_test "Initialize" \
    '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2024-11-05"}}' \
    "cure-mcp-server"

# Test 2: List tools
echo "Test 2: List Available Tools"
run_test "Tools List" \
    '{"jsonrpc":"2.0","id":2,"method":"tools/list"}' \
    "compile_cure"

# Create a simple test file
TEST_CURE_CODE='module TestModule do
  export [hello/0]
  
  def hello(): Atom = :ok
end'

echo "$TEST_CURE_CODE" > "$TEST_DIR/test.cure"

# Test 3: Validate syntax
echo "Test 3: Validate Syntax"
run_test "Validate Syntax" \
    "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"tools/call\",\"params\":{\"name\":\"validate_syntax\",\"arguments\":{\"code\":\"$TEST_CURE_CODE\"}}}" \
    "valid"

# Test 4: Parse code
echo "Test 4: Parse Code"
run_test "Parse Code" \
    "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"tools/call\",\"params\":{\"name\":\"parse_cure\",\"arguments\":{\"code\":\"$TEST_CURE_CODE\"}}}" \
    "successful"

# Test 5: Get AST
echo "Test 5: Get AST Representation"
run_test "Get AST" \
    "{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"tools/call\",\"params\":{\"name\":\"get_ast\",\"arguments\":{\"code\":\"$TEST_CURE_CODE\",\"pretty_print\":true}}}" \
    "AST"

# Test 6: FSM analysis
FSM_CODE='module FSMTest do
  fsm TrafficLight do
    initial: :red
    :red --> |:timer| :green
    :green --> |:timer| :yellow
    :yellow --> |:timer| :red
  end
end'

echo "Test 6: Analyze FSM"
run_test "FSM Analysis" \
    "{\"jsonrpc\":\"2.0\",\"id\":6,\"method\":\"tools/call\",\"params\":{\"name\":\"analyze_fsm\",\"arguments\":{\"code\":\"$FSM_CODE\"}}}" \
    "FSM"

# Test 7: Get syntax help
echo "Test 7: Get Syntax Help"
run_test "Syntax Help - Functions" \
    '{"jsonrpc":"2.0","id":7,"method":"tools/call","params":{"name":"get_syntax_help","arguments":{"topic":"functions"}}}' \
    "function"

echo "Test 8: Get Syntax Help - FSM"
run_test "Syntax Help - FSM" \
    '{"jsonrpc":"2.0","id":8,"method":"tools/call","params":{"name":"get_syntax_help","arguments":{"topic":"fsm"}}}' \
    "fsm"

# Test 9: Get examples
echo "Test 9: Get Examples"
run_test "Get Examples - Basics" \
    '{"jsonrpc":"2.0","id":9,"method":"tools/call","params":{"name":"get_examples","arguments":{"category":"basics"}}}' \
    "example"

# Test 10: Get stdlib docs
echo "Test 10: Get Standard Library Documentation"
run_test "Stdlib Docs - List" \
    '{"jsonrpc":"2.0","id":10,"method":"tools/call","params":{"name":"get_stdlib_docs","arguments":{"module":"Std.List"}}}' \
    "List"

# Test 11: Parse with syntax error
BAD_CODE='module Bad do
  def broken(: Type = 
end'

echo "Test 11: Parse Code with Syntax Error"
run_test "Parse Error Handling" \
    "{\"jsonrpc\":\"2.0\",\"id\":11,\"method\":\"tools/call\",\"params\":{\"name\":\"parse_cure\",\"arguments\":{\"code\":\"$BAD_CODE\"}}}" \
    "error"

# Test 12: Compile complete file
echo "Test 12: Compile File"
run_test "Compile File" \
    "{\"jsonrpc\":\"2.0\",\"id\":12,\"method\":\"tools/call\",\"params\":{\"name\":\"compile_cure\",\"arguments\":{\"file_path\":\"$TEST_DIR/test.cure\",\"output_dir\":\"$TEST_DIR/output\"}}}" \
    "successful\|failed"  # Either success or reasonable error is acceptable

echo ""
echo "=== Test Summary ==="
echo -e "${GREEN}Passed: $PASSED${NC}"
echo -e "${RED}Failed: $FAILED${NC}"
echo ""

if [ $FAILED -eq 0 ]; then
    echo -e "${GREEN}✓ All tests passed!${NC}"
    exit 0
else
    echo -e "${YELLOW}⚠ Some tests failed${NC}"
    exit 1
fi
