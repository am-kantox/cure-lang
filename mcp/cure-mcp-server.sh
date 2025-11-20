#!/usr/bin/env bash

# Cure MCP Server Startup Script
# Starts the Erlang-based MCP server for Cure language

set -e

# Get the directory where this script is located
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

# Check if Erlang is available
if ! command -v erl &> /dev/null; then
    echo "Error: Erlang is not installed or not in PATH" >&2
    exit 1
fi

# Check if jsone is available (JSON library for Erlang)
# We'll need to add this to rebar.config as a dependency
if ! erl -eval "application:load(jsone), halt(0)" -noshell 2>/dev/null; then
    echo "Warning: jsone library not found. Installing dependencies..." >&2
    cd "$PROJECT_ROOT"
    rebar3 get-deps 2>&1 | grep -v "^=="
fi

# Compile the MCP server module if needed
if [ ! -f "$PROJECT_ROOT/_build/default/lib/cure/ebin/cure_mcp_server.beam" ] && \
   [ ! -f "$PROJECT_ROOT/ebin/cure_mcp_server.beam" ]; then
    echo "Compiling MCP server..." >&2
    cd "$PROJECT_ROOT"
    erlc -o ebin -I src/parser -I src/fsm -I src/types mcp/cure_mcp_server.erl 2>&1 | grep -v "^Warning:"
fi

# Add all necessary paths
CODE_PATHS=(
    "$PROJECT_ROOT/ebin"
    "$PROJECT_ROOT/_build/default/lib/*/ebin"
    "$PROJECT_ROOT/_build/default/lib/cure/ebin"
)

# Build the path arguments for erl
PATH_ARGS=""
for path in "${CODE_PATHS[@]}"; do
    if [ -d "$path" ] || compgen -G "$path" > /dev/null; then
        PATH_ARGS="$PATH_ARGS -pa $path"
    fi
done

# Start the MCP server
# Use -noshell and -noinput for stdio communication
cd "$PROJECT_ROOT/mcp"
exec erl $PATH_ARGS \
    -noshell \
    -noinput \
    -s cure_mcp_server start
