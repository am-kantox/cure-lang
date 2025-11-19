# Cure MCP Server - Quick Start Guide

Get up and running with the Cure MCP server in 5 minutes.

## 1. Install Dependencies

```bash
cd /opt/Proyectos/Ammotion/cure
rebar3 get-deps
rebar3 compile
```

## 2. Test the Server

```bash
cd mcp
./cure-mcp-server.sh &
SERVER_PID=$!

# Send test request
echo '{"jsonrpc":"2.0","method":"initialize","params":{},"id":1}'

# Stop server
kill $SERVER_PID
```

## 3. Configure Claude Desktop

**File:** `~/.config/Claude/claude_desktop_config.json` (Linux)  
**File:** `~/Library/Application Support/Claude/claude_desktop_config.json` (macOS)

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

Replace `/opt/Proyectos/Ammotion/cure` with your actual Cure installation path.

## 4. Restart Claude Desktop

Close and reopen Claude Desktop completely.

## 5. Verify Connection

In Claude, you should see the Cure MCP tools available. Try asking:

```
"Can you show me Cure FSM syntax examples?"
```

Claude will use the `get_syntax_help` and `get_examples` tools automatically.

## Common Issues

### Server Not Starting

```bash
# Check Erlang version
erl -version

# Should be OTP 24 or later

# Recompile everything
cd /opt/Proyectos/Ammotion/cure
make clean
make all
```

### Tools Not Appearing

1. Check Claude config file location is correct
2. Ensure the `command` path is absolute
3. Restart Claude completely (not just refresh)
4. Check Claude logs:
   - macOS: `~/Library/Logs/Claude/`
   - Linux: `~/.config/Claude/logs/`

### JSON Errors

The MCP protocol uses JSON-RPC 2.0. Test manually:

```bash
cd /opt/Proyectos/Ammotion/cure/mcp

# Validate syntax test
echo '{"jsonrpc":"2.0","method":"tools/call","params":{"name":"validate_syntax","arguments":{"code":"module Test do\nend"}},"id":1}' | ./cure-mcp-server.sh
```

Expected response should include `"jsonrpc":"2.0"` and a result.

## Available Tools Quick Reference

| Tool | Purpose | Example Usage |
|------|---------|---------------|
| `validate_syntax` | Check code syntax | "Is this Cure code valid?" |
| `parse_cure` | Get AST structure | "Parse this Cure module" |
| `type_check_cure` | Type checking | "Check types in this code" |
| `compile_cure` | Full compilation | "Compile file.cure" |
| `analyze_fsm` | FSM analysis | "Analyze this FSM definition" |
| `get_syntax_help` | Language help | "Show me FSM syntax" |
| `get_examples` | Code examples | "Give me FSM examples" |
| `get_stdlib_docs` | Stdlib docs | "How does Std.List work?" |

## Next Steps

- See [README.md](README.md) for detailed documentation
- Check [examples/](../examples/) for Cure code samples
- Read [WARP.md](../WARP.md) for Cure language architecture

## Support

For issues or questions:
- GitHub Issues: https://github.com/am-kantox/cure-lang/issues
- Documentation: https://github.com/am-kantox/cure-lang
