# Cure MCP Server

Model Context Protocol (MCP) server for the Cure programming language. This server enables AI assistants like Claude to understand, analyze, and work with Cure code effectively.

## What is MCP?

The Model Context Protocol (MCP) is an open protocol that standardizes how AI assistants communicate with external tools and data sources. It enables AI systems to:

- Access language-specific tools and compilers
- Retrieve documentation and examples
- Analyze code structure and semantics
- Provide intelligent code assistance

## Features

The Cure MCP server provides the following tools for AI assistants:

### Compilation & Analysis Tools

- **`compile_cure`** - Compile Cure source files to BEAM bytecode
- **`parse_cure`** - Parse Cure code and return AST information
- **`type_check_cure`** - Type-check Cure code for errors
- **`validate_syntax`** - Quickly validate syntax without full compilation
- **`get_ast`** - Get detailed Abstract Syntax Tree representation

### FSM-Specific Tools

- **`analyze_fsm`** - Analyze finite state machine definitions and report structure

### Documentation & Learning Tools

- **`get_syntax_help`** - Get syntax help for Cure language features
  - Topics: functions, types, fsm, typeclasses, pattern_matching, modules, records, all
- **`get_examples`** - Retrieve Cure code examples by category
  - Categories: basics, fsm, typeclasses, advanced, all
- **`get_stdlib_docs`** - Get standard library documentation
  - Modules: Std.List, Std.Io, Std.Fsm, Std.Option, Std.Result, all

## Installation

### Prerequisites

- Erlang/OTP 24 or later
- rebar3 (for building dependencies)
- Node.js 16+ (for npm/npx compatibility with MCP clients)

### Setup

1. **Install dependencies:**

```bash
cd /opt/Proyectos/Ammotion/cure
rebar3 get-deps
rebar3 compile
```

2. **Verify the MCP server:**

```bash
cd mcp
./cure-mcp-server.sh
# Press Ctrl+C to exit
```

## Configuration

### Claude Desktop

To use the Cure MCP server with Claude Desktop, add it to your Claude configuration file:

**Location:**
- macOS: `~/Library/Application Support/Claude/claude_desktop_config.json`
- Linux: `~/.config/Claude/claude_desktop_config.json`
- Windows: `%APPDATA%\Claude\claude_desktop_config.json`

**Configuration:**

```json
{
  "mcpServers": {
    "cure": {
      "command": "/opt/Proyectos/Ammotion/cure/mcp/cure-mcp-server.sh",
      "args": []
    }
  }
}
```

Or if you've installed it via npm:

```json
{
  "mcpServers": {
    "cure": {
      "command": "npx",
      "args": ["cure-mcp-server"]
    }
  }
}
```

### Other MCP Clients

The server uses JSON-RPC 2.0 over stdio, so it works with any MCP-compatible client:

```bash
# Start the server
./cure-mcp-server.sh

# The server reads JSON-RPC requests from stdin
# and writes responses to stdout
```

## Usage Examples

Once configured, you can ask Claude to use Cure-specific tools:

### Example 1: Validate Syntax

```
User: Can you validate this Cure code for syntax errors?

module Test do
  def add(x: Int, y: Int): Int = x + y
end
```

Claude will use the `validate_syntax` tool to check the code.

### Example 2: Get FSM Documentation

```
User: Show me how to use FSMs in Cure
```

Claude will use `get_syntax_help` with topic "fsm" and `get_examples` with category "fsm".

### Example 3: Analyze Code

```
User: Parse this Cure code and explain its structure:

module Calculator do
  record State do
    total: Int
  end
  
  def add(state: State, n: Int): State =
    State{total: state.total + n}
end
```

Claude will use `parse_cure` and `get_ast` to analyze the code structure.

### Example 4: Compile a File

```
User: Compile the file examples/06_fsm_traffic_light.cure
```

Claude will use `compile_cure` to build the file and report results.

## Tool Details

### compile_cure

Compiles a Cure source file through the full pipeline: lexing, parsing, type-checking, and code generation.

**Input:**
- `file_path` (required): Path to `.cure` file
- `output_dir` (optional): Output directory for `.beam` files

**Output:**
- Success: List of generated BEAM files
- Error: Detailed compilation error with location

### parse_cure

Parses Cure source code and returns AST summary.

**Input:**
- `code` (required): Cure source code as string

**Output:**
- AST summary with module information
- Parse errors with line/column information

### type_check_cure

Performs type checking on Cure code.

**Input:**
- `code` (required): Cure source code as string

**Output:**
- Type checking success or detailed type errors

### analyze_fsm

Extracts and analyzes FSM definitions from code.

**Input:**
- `code` (required): Cure source code with FSM definitions

**Output:**
- FSM structure including states, transitions, initial state
- State machine analysis and validation

### get_syntax_help

Provides syntax reference for Cure language features.

**Input:**
- `topic` (required): One of: functions, types, fsm, typeclasses, pattern_matching, modules, records, all

**Output:**
- Syntax examples and explanations for the requested topic

### get_examples

Retrieves example code from the Cure examples directory.

**Input:**
- `category` (required): One of: basics, fsm, typeclasses, advanced, all

**Output:**
- Commented example code demonstrating the requested features

### get_stdlib_docs

Provides documentation for Cure standard library modules.

**Input:**
- `module` (required): One of: Std.List, Std.Io, Std.Fsm, Std.Option, Std.Result, all

**Output:**
- Function signatures, descriptions, and usage examples

## Architecture

The MCP server is implemented in Erlang and integrates directly with the Cure compiler:

```
┌─────────────────┐
│  MCP Client     │
│  (Claude, etc)  │
└────────┬────────┘
         │ JSON-RPC 2.0 over stdio
         │
┌────────▼────────────┐
│  cure_mcp_server    │
│  (Erlang)           │
├─────────────────────┤
│ - Tool routing      │
│ - JSON encoding     │
│ - Error handling    │
└────────┬────────────┘
         │
    ┌────┴─────────┬──────────┬──────────┐
    │              │          │          │
┌───▼────┐  ┌─────▼─────┐ ┌─▼────┐ ┌───▼─────┐
│ Lexer  │  │  Parser   │ │Types │ │ Codegen │
└────────┘  └───────────┘ └──────┘ └─────────┘
```

## Development

### Building

```bash
cd /opt/Proyectos/Ammotion/cure
make all
erlc -o ebin -I src/parser -I src/fsm -I src/types mcp/cure_mcp_server.erl
```

### Testing

Test the server manually using echo and pipes:

```bash
# Test initialize
echo '{"jsonrpc":"2.0","method":"initialize","params":{},"id":1}' | ./cure-mcp-server.sh

# Test tools list
echo '{"jsonrpc":"2.0","method":"tools/list","params":{},"id":2}' | ./cure-mcp-server.sh

# Test validate_syntax
echo '{"jsonrpc":"2.0","method":"tools/call","params":{"name":"validate_syntax","arguments":{"code":"module Test do\nend"}},"id":3}' | ./cure-mcp-server.sh
```

### Adding New Tools

To add a new tool:

1. Add tool definition to `handle_tools_list/2` with schema
2. Add handler function (e.g., `handle_my_tool/1`)
3. Register handler in `init_state/1` tool_handlers map
4. Implement tool logic using Cure compiler modules

## Troubleshooting

### Server won't start

- Check Erlang is installed: `erl -version`
- Verify rebar3 dependencies: `rebar3 get-deps`
- Check for compilation errors: `make all`

### JSON parsing errors

- The server expects one JSON-RPC request per line
- Ensure requests are properly formatted with `jsonrpc: "2.0"`

### Compiler module not found

- Ensure all Cure compiler modules are compiled
- Check `ebin/` directory for `.beam` files
- Try `make clean && make all`

### Tools not appearing in Claude

- Restart Claude Desktop after config changes
- Check the config file path matches your OS
- View Claude logs for connection errors

## Contributing

Contributions welcome! Areas for improvement:

- Additional tools for documentation generation
- Enhanced FSM verification tools  
- Code formatting tool implementation
- Performance optimizations
- Extended error diagnostics

## License

MIT License - see project root LICENSE file.

## See Also

- [Cure Language Documentation](../README.md)
- [MCP Protocol Specification](https://modelcontextprotocol.io/)
- [Claude Desktop](https://claude.ai/desktop)
