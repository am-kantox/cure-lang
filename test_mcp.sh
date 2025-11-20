#!/bin/bash

# Test MCP server

echo "Testing MCP server..."

# Send initialize request
echo '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}' | /opt/Proyectos/Ammotion/cure/cure-mcp start &

# Wait a bit for response
sleep 1

# Kill the server
killall -9 beam.smp 2>/dev/null

echo "Done"
