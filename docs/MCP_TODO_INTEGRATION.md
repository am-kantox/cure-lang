# MCP TODO Integration

**Date**: November 25, 2025  
**Purpose**: Document integration of TODO-2025-11-24.md into the Cure MCP server as a queryable resource

## Overview

The Cure project's comprehensive TODO and status document (`TODO-2025-11-24.md`) has been integrated into the Model Context Protocol (MCP) server as a **resource**. This enables AI assistants like Claude to query project status, audit results, and production readiness information.

## Why MCP Resources?

MCP (Model Context Protocol) defines three types of context that servers can expose:

1. **Tools** - Executable functions (compile, parse, analyze, etc.)
2. **Resources** - Queryable data sources (documentation, project status, etc.)
3. **Prompts** - Template workflows for common tasks

The TODO document fits naturally as a **resource** because:
- It provides static/semi-static information about project state
- AI assistants need to read it, not execute it
- It's analogous to documentation or configuration files
- Resources support versioning and updates

## Why Not LSP?

The Language Server Protocol (LSP) integration was **not modified** because:
- LSP focuses on per-file code intelligence (completions, diagnostics, hover)
- LSP does not have a concept of "project status resources"
- LSP is for IDE features, not project metadata
- MCP is the correct protocol for exposing project-level information to AI assistants

## Implementation Details

### Resource URI

```
cure://project/todo
```

This custom URI scheme follows MCP best practices for language-specific resources.

### Resource Metadata

```json
{
  "uri": "cure://project/todo",
  "name": "Project TODO & Status",
  "description": "Comprehensive project status, audit results, and production readiness assessment (90% complete)",
  "mimeType": "text/markdown"
}
```

### Integration Points

**1. Server Capabilities** (`cure_mcp_server.erl:35-38`)
```erlang
resources => #{
    subscribe => false,
    listChanged => false
}
```

**2. Resource List Handler** (`cure_mcp_server.erl:357-377`)
- Returns list of available resources
- Currently exposes one resource: `cure://project/todo`

**3. Resource Read Handler** (`cure_mcp_server.erl:380-408`)
- Reads `../TODO-2025-11-24.md` relative to MCP server location
- Returns full markdown content
- Handles file read errors gracefully

**4. Request Router** (`cure_mcp_server.erl:159-160`)
- Added `resources/read` method to request dispatcher

## Usage Examples

### From Claude Desktop

```
User: What's the current status of the Cure project?
```

Claude will:
1. Call `resources/list` to discover available resources
2. See `cure://project/todo` resource
3. Call `resources/read` with that URI
4. Parse the markdown and provide a summary

### From MCP Client

**List resources:**
```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "method": "resources/list",
  "params": {}
}
```

**Response:**
```json
{
  "jsonrpc": "2.0",
  "id": 1,
  "result": {
    "resources": [
      {
        "uri": "cure://project/todo",
        "name": "Project TODO & Status",
        "description": "Comprehensive project status, audit results, and production readiness assessment (90% complete)",
        "mimeType": "text/markdown"
      }
    ]
  }
}
```

**Read resource:**
```json
{
  "jsonrpc": "2.0",
  "id": 2,
  "method": "resources/read",
  "params": {
    "uri": "cure://project/todo"
  }
}
```

**Response:**
```json
{
  "jsonrpc": "2.0",
  "id": 2,
  "result": {
    "contents": [
      {
        "uri": "cure://project/todo",
        "mimeType": "text/markdown",
        "text": "# Cure Programming Language - TODO Audit (2025-11-24/25)\n\n..."
      }
    ]
  }
}
```

## Benefits

1. **Discoverability**: AI assistants can discover project status automatically
2. **Consistency**: Single source of truth for project status
3. **Up-to-date**: Always reflects latest audit results
4. **Structured**: Markdown format is easy for AI to parse
5. **Queryable**: AI can answer questions about project status

## Testing

Run the test script:
```bash
cd /opt/Proyectos/Ammotion/cure/mcp
./test_resources.sh
```

This tests:
1. Resource listing (should return cure://project/todo)
2. Resource reading (should return TODO.md content)
3. Invalid URI handling (should return error)

## Future Enhancements

Potential additional resources:

1. **`cure://project/changelog`** - CHANGELOG.md
2. **`cure://project/roadmap`** - Future feature plans
3. **`cure://docs/syntax`** - Complete syntax reference
4. **`cure://docs/stdlib`** - Standard library API reference
5. **`cure://project/benchmarks`** - Performance benchmark results
6. **`cure://project/tests`** - Test suite status and coverage

## Related Documentation

- `mcp/README.md` - MCP server overview and usage
- `mcp/ARCHITECTURE.md` - Detailed architecture documentation
- `TODO-2025-11-24.md` - The actual status document
- MCP Specification: https://spec.modelcontextprotocol.io/

## Validation Checklist

✅ **Implementation**
- [x] Added `resources` capability to server state
- [x] Implemented `handle_resources_list/2`
- [x] Implemented `handle_resources_read/2`
- [x] Added `resources/read` to request router
- [x] File path resolution works correctly

✅ **Documentation**
- [x] Updated MCP README.md with resources section
- [x] Updated ARCHITECTURE.md with implementation details
- [x] Created this integration guide
- [x] Added code comments

✅ **Testing**
- [x] Server compiles without errors
- [x] Created test script for resources
- [x] Manual testing with JSON-RPC requests

✅ **Correctness**
- [x] Follows MCP specification for resources
- [x] Returns proper JSON-RPC 2.0 responses
- [x] Handles errors gracefully
- [x] Uses appropriate MIME type (text/markdown)

## Conclusion

The TODO-2025-11-24.md integration is **complete and production-ready**. AI assistants using the Cure MCP server can now query project status, audit results, and production readiness information through the standard MCP resources interface.

This integration follows best practices for MCP resource implementation and provides a foundation for exposing additional project metadata in the future.
