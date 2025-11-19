# Cure MCP Integration

The Cure programming language now includes a Model Context Protocol (MCP) server that enables AI assistants to interact with the Cure compiler and toolchain.

## What is MCP?

The Model Context Protocol (MCP) is an open standard that allows AI assistants like Claude to:
- Access specialized tools and compilers
- Retrieve language-specific documentation
- Analyze code structure
- Provide intelligent assistance for domain-specific languages

## Features

The Cure MCP server provides AI assistants with:

### Compilation Tools
- **Compile** - Full compilation from source to BEAM bytecode
- **Parse** - Syntax parsing and AST generation
- **Type Check** - Type verification and error detection
- **Validate** - Quick syntax validation

### FSM Tools
- **Analyze FSM** - Extract and analyze finite state machine definitions
- FSM structure inspection
- State and transition analysis

### Documentation Tools
- **Syntax Help** - Get syntax examples for language features
- **Code Examples** - Access curated example code
- **Stdlib Docs** - Standard library documentation

## Quick Start

### 1. Install and Build

```bash
cd /opt/Proyectos/Ammotion/cure
rebar3 get-deps
rebar3 compile
```

### 2. Configure Claude Desktop

Edit your Claude configuration file:
- **Linux**: `~/.config/Claude/claude_desktop_config.json`
- **macOS**: `~/Library/Application Support/Claude/claude_desktop_config.json`

```json
{
  "mcpServers": {
    "cure": {
      "command": "/path/to/cure/mcp/cure-mcp-server.sh",
      "args": []
    }
  }
}
```

### 3. Restart Claude

Close and reopen Claude Desktop completely.

### 4. Try It Out

Ask Claude questions about Cure:
- "Show me how to define an FSM in Cure"
- "Validate this Cure code: `module Test do ... end`"
- "What functions are available in Std.List?"
- "Compile examples/06_fsm_traffic_light.cure"

## Available Tools

| Tool | Description |
|------|-------------|
| `compile_cure` | Compile Cure source to BEAM bytecode |
| `parse_cure` | Parse code and return AST information |
| `type_check_cure` | Type-check code for errors |
| `validate_syntax` | Quick syntax validation |
| `get_ast` | Get detailed AST representation |
| `analyze_fsm` | Analyze FSM definitions |
| `get_syntax_help` | Language syntax reference |
| `get_examples` | Example code by category |
| `get_stdlib_docs` | Standard library documentation |

## Documentation

Comprehensive documentation available in `mcp/`:
- **[README.md](../mcp/README.md)** - Complete user guide
- **[QUICKSTART.md](../mcp/QUICKSTART.md)** - 5-minute setup guide
- **[ARCHITECTURE.md](../mcp/ARCHITECTURE.md)** - Technical architecture details

## Example Usage

### Validate Syntax

```
User: Is this Cure code valid?

module Calculator do
  def add(x: Int, y: Int): Int = x + y
end
```

Claude will use the `validate_syntax` tool and report results.

### Get FSM Examples

```
User: Show me FSM examples in Cure
```

Claude will use `get_examples` with category "fsm" to retrieve FSM example code.

### Compile Code

```
User: Compile the traffic light example
```

Claude will use `compile_cure` on the FSM traffic light example.

## Architecture

The MCP server is implemented in Erlang and integrates directly with the Cure compiler:

```
Claude Desktop ←→ JSON-RPC ←→ cure_mcp_server.erl ←→ Cure Compiler
                   (stdio)                              (modules)
```

**Key Components:**
- **cure_mcp_server.erl** - Main MCP protocol implementation
- **cure-mcp-server.sh** - Startup script with dependency checking
- **Tool handlers** - Direct integration with compiler modules

## Benefits

### For AI Assistants
- Direct access to Cure compiler
- Real-time syntax validation
- Accurate documentation
- FSM-specific analysis tools

### For Developers
- Intelligent code completion suggestions
- Syntax error detection
- Quick documentation lookup
- Example code retrieval

### For the Cure Project
- Better discoverability
- Enhanced learning experience
- Improved developer onboarding
- AI-assisted development

## Testing

Test the MCP server:

```bash
cd mcp
./test_mcp.sh
```

This runs basic tests for:
- Protocol initialization
- Tool listing
- Syntax help
- Code validation

## Troubleshooting

### Server Won't Start
- Verify Erlang installation: `erl -version`
- Check dependencies: `rebar3 get-deps`
- Rebuild: `make clean && make all`

### Tools Not Appearing
- Verify Claude config path
- Use absolute paths in config
- Restart Claude completely
- Check Claude logs

### Compilation Errors
Ensure all Cure modules are compiled:
```bash
cd /opt/Proyectos/Ammotion/cure
make all
```

## Contributing

The MCP server is extensible. To add new tools:

1. Define tool schema in `handle_tools_list/2`
2. Implement handler function
3. Register in `init_state/1`

See [ARCHITECTURE.md](../mcp/ARCHITECTURE.md) for details.

## Future Enhancements

Planned improvements:
- Code formatting tool
- Multi-file project analysis
- Interactive debugging support
- Test generation tools
- Performance profiling integration

## Resources

- [MCP Protocol Specification](https://modelcontextprotocol.io/)
- [Claude Desktop](https://claude.ai/desktop)
- [Cure Language Documentation](../README.md)
- [MCP Server Source](../mcp/)

## License

MIT License - same as the Cure language project.
