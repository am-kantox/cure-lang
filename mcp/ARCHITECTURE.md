# Cure MCP Server Architecture

This document describes the architecture and implementation details of the Cure MCP (Model Context Protocol) server.

## Overview

The Cure MCP server is an Erlang application that implements the Model Context Protocol to enable AI assistants to interact with the Cure programming language compiler and toolchain.

## Components

### 1. Core Server (`cure_mcp_server.erl`)

The main server module implementing JSON-RPC 2.0 over stdio.

**Key Functions:**
- `start/0, start/1` - Initialize and start the server
- `loop/1` - Main event loop reading from stdin
- `handle_request/2` - Route incoming JSON-RPC requests
- `read_jsonrpc_request/0` - Parse JSON-RPC from stdin
- `send_jsonrpc_response/1` - Send JSON-RPC to stdout

**State Management:**
```erlang
-record(server_state, {
    capabilities = #{
        tools => #{},
        resources => #{},
        prompts => #{}
    },
    tool_handlers = #{}
}).
```

The server maintains a registry of tool handlers as a map from tool name (binary) to handler function.

### 2. Protocol Implementation

#### MCP Methods Supported

1. **`initialize`** - Protocol handshake
   - Returns server info and capabilities
   - Protocol version: `2024-11-05`

2. **`tools/list`** - List available tools
   - Returns tool definitions with JSON schemas

3. **`tools/call`** - Execute a tool
   - Routes to registered tool handlers
   - Returns tool output or errors

4. **`resources/list`** - List resources (currently empty)

5. **`prompts/list`** - List prompts (currently empty)

#### JSON-RPC 2.0 Format

**Request:**
```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "method": "tools/call",
  "params": {
    "name": "validate_syntax",
    "arguments": {
      "code": "module Test do\nend"
    }
  }
}
```

**Response:**
```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "result": {
    "content": [
      {
        "type": "text",
        "text": "✓ Syntax is valid"
      }
    ]
  }
}
```

### 3. Tool Implementations

#### Compilation Tools

**`handle_compile/1`**
- Full compilation pipeline: lex → parse → typecheck → codegen
- Creates BEAM bytecode files
- Returns compilation results or detailed errors

**`handle_parse/1`**
- Lexical analysis and parsing
- Returns AST summary

**`handle_type_check/1`**
- Type checking without code generation
- Reports type errors with locations

**`handle_validate_syntax/1`**
- Fast syntax validation
- Skips type checking and codegen

**`handle_get_ast/1`**
- Detailed AST representation
- Optional pretty-printing

#### FSM Tools

**`handle_analyze_fsm/1`**
- Extracts FSM definitions from AST
- Reports states, transitions, initial state
- Uses `extract_fsms/1` helper

#### Documentation Tools

**`handle_syntax_help/1`**
- Provides inline syntax reference
- Topics: modules, functions, types, records, fsm, typeclasses, pattern_matching

**`handle_get_examples/1`**
- Reads example files from `examples/` directory
- Categories: basics, fsm, typeclasses, advanced

**`handle_stdlib_docs/1`**
- Standard library documentation
- Modules: Std.List, Std.Io, Std.Fsm, Std.Option, Std.Result

### 4. Compiler Integration

The MCP server integrates with Cure compiler modules:

```
cure_mcp_server
    ↓
cure_lexer:tokenize/1
    ↓
cure_parser:parse/1
    ↓
cure_typechecker:typecheck/1
    ↓
cure_codegen:generate/2
```

All compiler modules are called directly as Erlang functions, ensuring type safety and error handling.

### 5. Error Handling

**Error Response Format:**
```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "error": {
    "code": -32603,
    "message": "Tool execution failed: ..."
  }
}
```

**Error Codes:**
- `-32601` - Method not found
- `-32602` - Invalid params (unknown tool)
- `-32603` - Internal error (tool execution failure)

**Error Propagation:**
1. Compiler errors are caught and formatted
2. Stack traces included in error messages
3. Location information preserved when available

### 6. Startup Script (`cure-mcp-server.sh`)

Shell script that:
1. Validates Erlang installation
2. Checks for jsone dependency
3. Compiles MCP server if needed
4. Sets up code paths for all modules
5. Starts Erlang with MCP server

**Key Features:**
- Auto-compilation on first run
- Dependency checking
- Clean stdio communication (stderr for logs, stdout for JSON-RPC)

## Data Flow

```
┌──────────────┐
│ MCP Client   │
│ (Claude)     │
└──────┬───────┘
       │ stdin/stdout
       │
┌──────▼────────────────────────────────┐
│ cure_mcp_server                        │
│                                        │
│  read_jsonrpc_request()                │
│         ↓                              │
│  handle_request(Request, State)        │
│         ↓                              │
│  lookup tool_handler in State          │
│         ↓                              │
│  Handler(Arguments)                    │
│         ↓                              │
│  format_success() / format_error()     │
│         ↓                              │
│  send_jsonrpc_response(Response)       │
└────────┬──────────────────────────────┘
         │
    ┌────┴────┐
    │         │
┌───▼────┐ ┌──▼────────┐
│ Lexer  │ │  Examples │
│ Parser │ │  Docs     │
│ Types  │ │  Help     │
│ FSM    │ │           │
└────────┘ └───────────┘
```

## Extension Points

### Adding a New Tool

1. **Define tool schema** in `handle_tools_list/2`:
```erlang
#{
    <<"name">> => <<"my_tool">>,
    <<"description">> => <<"Tool description">>,
    <<"inputSchema">> => #{
        <<"type">> => <<"object">>,
        <<"properties">> => #{
            <<"param">> => #{
                <<"type">> => <<"string">>,
                <<"description">> => <<"Parameter description">>
            }
        },
        <<"required">> => [<<"param">>]
    }
}
```

2. **Implement handler** function:
```erlang
handle_my_tool(Args) ->
    Param = maps:get(<<"param">>, Args),
    Result = do_work(Param),
    format_success(<<"Success">>, Result).
```

3. **Register handler** in `init_state/1`:
```erlang
tool_handlers = #{
    ...
    <<"my_tool">> => fun handle_my_tool/1
}
```

### Adding Resources

Resources provide file-like access to data. To add:

1. Implement `handle_resources_list/2` to return resource URIs
2. Implement `handle_resources_read/2` to return resource content
3. Update server capabilities in `init_state/1`

### Adding Prompts

Prompts are templates for common tasks. To add:

1. Implement `handle_prompts_list/2` to return prompt definitions
2. Implement `handle_prompts_get/2` to return prompt content
3. Update server capabilities in `init_state/1`

## Performance Considerations

- **Startup Time**: ~100-200ms (Erlang VM + module loading)
- **Tool Execution**: Varies by tool
  - `validate_syntax`: ~10-50ms
  - `compile_cure`: ~100-500ms (full pipeline)
  - `get_syntax_help`: <5ms (static data)
- **Memory**: ~50-100MB (Erlang VM + compiler)

**Optimizations:**
- Tools reuse compiler modules (no subprocess spawning)
- Examples read on-demand (not preloaded)
- AST kept in memory during tool execution

## Security Considerations

1. **File System Access**: Tools can read/write files
   - `compile_cure` writes to specified output directory
   - `get_examples` reads from `examples/` directory
   - No arbitrary file access from user input

2. **Code Execution**: 
   - Compilation does not execute user code
   - FSM analysis is static (no runtime evaluation)

3. **Resource Limits**:
   - No built-in timeouts (handled by MCP client)
   - No memory limits (rely on OS/Erlang VM)

## Testing Strategy

1. **Unit Tests**: Test individual tool handlers
2. **Integration Tests**: Test full JSON-RPC flow
3. **Manual Tests**: Use `test_mcp.sh` script
4. **Client Tests**: Test with Claude Desktop

## Future Enhancements

### Short Term
- Add code formatting tool
- Implement resource providers for docs
- Add prompt templates for common tasks
- Enhanced error messages with suggestions

### Long Term
- Incremental compilation support
- Project-aware tools (multi-file analysis)
- Interactive debugging tools
- Performance profiling integration
- Test generation tools

## Dependencies

- **Erlang/OTP 24+**: Runtime and compiler
- **jsone**: JSON encoding/decoding
- **Cure Compiler**: All compiler modules (lexer, parser, types, codegen, fsm)

## Configuration

No configuration file needed. Server behavior controlled by:
- Tool handler implementations
- Cure compiler configuration
- Startup script environment

## Deployment

### Development
```bash
./cure-mcp-server.sh
```

### Production (via npm)
```bash
npm install -g cure-mcp-server
cure-mcp
```

### Claude Desktop
Add to config file:
```json
{
  "mcpServers": {
    "cure": {
      "command": "/path/to/cure-mcp-server.sh"
    }
  }
}
```

## Monitoring & Debugging

**Logging:**
- Logs written to stderr (not stdout)
- Uses `error_logger:info_msg/2` and `error_logger:error_msg/2`
- Log format: `[Cure MCP] message`

**Debug Mode:**
- Set `ERL_LIBS` environment variable for additional paths
- Use `-s cure_mcp_server start` for interactive debugging

**Common Issues:**
- "Module not found": Check code paths in startup script
- "JSON parse error": Ensure proper JSON-RPC format
- "Tool timeout": Increase client timeout settings

## License

MIT License - same as Cure language project.
