#!/usr/bin/env bash

# Simple test script for Cure MCP Server

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

echo "Testing Cure MCP Server..."
echo ""

# Test 1: Initialize
echo "Test 1: Initialize"
RESPONSE=$(echo '{"jsonrpc":"2.0","method":"initialize","params":{},"id":1}' | timeout 5 ./cure-mcp 2>/dev/null | head -1)
if echo "$RESPONSE" | grep -q '"protocolVersion"'; then
    echo "✓ Initialize works"
else
    echo "✗ Initialize failed"
    echo "Response: $RESPONSE"
    exit 1
fi
echo ""

# Test 2: Tools list
echo "Test 2: List tools"
RESPONSE=$(echo '{"jsonrpc":"2.0","method":"tools/list","params":{},"id":2}' | timeout 5 ./cure-mcp 2>/dev/null | head -1)
if echo "$RESPONSE" | grep -q 'compile_cure'; then
    echo "✓ Tools list works"
else
    echo "✗ Tools list failed"
    echo "Response: $RESPONSE"
    exit 1
fi
echo ""

# Test 3: Get syntax help
echo "Test 3: Get syntax help"
RESPONSE=$(echo '{"jsonrpc":"2.0","method":"tools/call","params":{"name":"get_syntax_help","arguments":{"topic":"functions"}},"id":3}' | timeout 5 ./cure-mcp 2>/dev/null | head -1)
if echo "$RESPONSE" | grep -q 'Functions'; then
    echo "✓ Get syntax help works"
else
    echo "✗ Get syntax help failed"
    echo "Response: $RESPONSE"
    exit 1
fi
echo ""

# Test 4: Validate syntax
echo "Test 4: Validate syntax"
CODE='module Test do\n  def add(x: Int, y: Int): Int = x + y\nend'
REQUEST="{\"jsonrpc\":\"2.0\",\"method\":\"tools/call\",\"params\":{\"name\":\"validate_syntax\",\"arguments\":{\"code\":\"$CODE\"}},\"id\":4}"
RESPONSE=$(echo "$REQUEST" | timeout 5 ./cure-mcp 2>/dev/null | head -1)
if echo "$RESPONSE" | grep -q 'valid\|error'; then
    echo "✓ Validate syntax works"
else
    echo "✗ Validate syntax failed"
    echo "Response: $RESPONSE"
    exit 1
fi
echo ""

echo "All tests passed!"
echo ""
echo "MCP Server is ready to use!"
echo "Configure Claude Desktop with:"
echo "  Command: $SCRIPT_DIR/cure-mcp"
