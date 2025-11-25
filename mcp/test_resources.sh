#!/bin/bash
# Test MCP resources functionality

echo "Testing MCP resources endpoint..."
echo ""

# Test 1: List resources
echo "Test 1: List resources"
echo '{"jsonrpc":"2.0","id":1,"method":"resources/list","params":{}}' | ../cure-mcp 2>/dev/null | head -1
echo ""

# Test 2: Read TODO resource
echo "Test 2: Read TODO resource (first 500 chars)"
echo '{"jsonrpc":"2.0","id":2,"method":"resources/read","params":{"uri":"cure://project/todo"}}' | ../cure-mcp 2>/dev/null | head -1 | cut -c1-500
echo "..."
echo ""

# Test 3: Read invalid resource
echo "Test 3: Read invalid resource (should error)"
echo '{"jsonrpc":"2.0","id":3,"method":"resources/read","params":{"uri":"cure://invalid/resource"}}' | ../cure-mcp 2>/dev/null | head -1
echo ""

echo "Tests completed!"
