#!/usr/bin/env bash
# Wrapper script for cure-mcp to be used with LunarVim and other MCP clients
# This ensures the proper environment and paths are set up before running cure-mcp

set -e

# Get the directory where this script is located
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Ensure the project is built
if [ ! -d "$SCRIPT_DIR/_build/ebin" ] || [ ! -f "$SCRIPT_DIR/_build/ebin/cure_mcp_server.beam" ]; then
    echo "ERROR: Cure MCP server not built. Please run 'make all' in $SCRIPT_DIR" >&2
    exit 1
fi

# Set environment variables if needed
export CURE_HOME="$SCRIPT_DIR"

# Execute cure-mcp with all arguments passed through
exec "$SCRIPT_DIR/cure-mcp" "$@"
