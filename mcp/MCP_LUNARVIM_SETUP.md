# Cure MCP Server Setup for LunarVim

This guide explains how to use the Cure MCP server with LunarVim and other MCP clients.

## Prerequisites

- Erlang/OTP 20+ installed
- Cure project built with `make all`
- LunarVim or another MCP client

## Building the MCP Server

The MCP server is automatically built when you run:

```bash
make all
```

Or you can build just the MCP server:

```bash
make mcp
```

This compiles the MCP server modules (`cure_mcp_server.erl` and `cure_mcp_user.erl`) to `_build/ebin/`.

## Running the MCP Server

You have two options to run the MCP server:

### Option 1: Direct escript (Recommended)

```bash
/home/am/Proyectos/Ammotion/cure/cure-mcp
```

The `cure-mcp` escript automatically:
- Locates the script directory
- Adds required code paths (`_build/ebin`, `_build/lsp`, `_build/lib`, etc.)
- Starts the MCP server

### Option 2: Wrapper script

```bash
/home/am/Proyectos/Ammotion/cure/cure-mcp-wrapper.sh
```

The wrapper script additionally:
- Validates that the MCP server is built
- Sets `CURE_HOME` environment variable
- Provides clear error messages if something is missing

## LunarVim Configuration

Add to your LunarVim MCP configuration:

```lua
{
  name = "cure-mcp",
  command = "/home/am/Proyectos/Ammotion/cure/cure-mcp",
  args = {}
}
```

Or using the wrapper:

```lua
{
  name = "cure-mcp",
  command = "/home/am/Proyectos/Ammotion/cure/cure-mcp-wrapper.sh",
  args = {}
}
```

For a more portable configuration using Vim's path expansion:

```lua
{
  name = "cure-mcp",
  command = vim.fn.expand("~/Proyectos/Ammotion/cure/cure-mcp"),
  args = {}
}
```

## Available Commands

The MCP server supports:

- `--version` - Display version information
- `--help` - Show help message
- `start` (or no arguments) - Start the MCP server

## Testing the Server

Test that the server is working:

```bash
# Test version
./cure-mcp --version

# Expected output: Cure MCP Server version 0.1.0

# Test help
./cure-mcp --help

# Expected output: Usage information
```

## MCP Server Capabilities

The Cure MCP server provides:

1. **Compile Cure Code** - Compile `.cure` source files to BEAM bytecode
2. **Type Check** - Perform dependent type checking on Cure code
3. **Parse Cure** - Parse Cure source and return AST
4. **Validate FSM** - Validate finite state machine definitions
5. **Get Standard Library Info** - Query standard library modules and functions

## Troubleshooting

### "The task "cure_mcp_server" could not be found"

This means the MCP server modules are not compiled. Run:

```bash
make mcp
```

### "cure_mcp_server.beam not found"

Ensure the project is built:

```bash
make all
```

### Server not responding

Check that the server starts successfully:

```bash
./cure-mcp --version
```

If this fails, check the Erlang installation and code paths.

## Files

- `cure-mcp` - Main escript executable
- `cure-mcp-wrapper.sh` - Wrapper script with validation
- `mcp/cure_mcp_server.erl` - MCP server implementation
- `mcp/cure_mcp_user.erl` - User-facing MCP interface

## More Information

See the `mcp/` directory for:
- `ARCHITECTURE.md` - MCP server architecture
- `LUNARVIM_INTEGRATION.md` - Detailed LunarVim integration guide
- `QUICKSTART.md` - Quick start guide
- `README.md` - MCP server documentation
