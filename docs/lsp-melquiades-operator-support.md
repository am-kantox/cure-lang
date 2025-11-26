# LSP Support for Melquíades Operator (`|->`)

## Overview

The Cure LSP now provides hover documentation for the Melquíades operator (`|->`), which is used to send messages asynchronously to GenServer processes.

## Implementation

### Changes Made

1. **Enhanced `cure_lsp_analyzer.erl`**:
   - Added `find_operator_at_position/3` function to detect operators at cursor position
   - Added `extract_operator_at_position/2` helper to extract operators from line text
   - Modified `get_hover_from_module/4` to check for operators before other symbols
   - Updated call chain to pass text through hover functions

2. **Operator Detection Logic**:
   - Searches for `|->` in a 3-character window around the cursor position
   - Validates that cursor is within the operator boundaries
   - Works regardless of surrounding whitespace

3. **Hover Information**:
   - Provides comprehensive documentation about the Melquíades operator
   - Explains async message sending behavior using `gen_server:cast/2`
   - Documents the three forms of GenServer names (local, global, via)
   - Includes origin story (named after character from García Márquez)

### Technical Details

The operator detection works by:

1. Extracting the line of text at the cursor position
2. Searching for the `|->` pattern within a few characters of the cursor
3. Verifying the cursor is within the operator's character range
4. Returning the hover information from the existing `get_symbol_hover_info/3` clause

### Hover Content

When hovering over `|->`, users see:

```cure
message |-> target
```

**Melquíades Operator** (|->)

Sends a message asynchronously to a GenServer process.

Named after the character from Gabriel García Márquez's "One Hundred Years of Solitude".

**Behavior:**
- Uses `gen_server:cast/2` (fire-and-forget)
- Always returns `None`
- Records are auto-converted to maps with `__from__` key

**Target formats:**
- Local name: `:my_server`
- Global: `{:global, :name}`
- Via registry: `{:via, Registry, key}`

## Testing

A comprehensive test suite was created in `test/lsp_melquiades_hover_test.erl` that verifies:

- Hover works when cursor is on any character of `|->`
- Hover works with and without surrounding whitespace
- Hover works on actual code from `examples/melquiades_demo.cure`
- Other symbols still work correctly (backward compatibility)

All tests pass successfully.

## Usage

In a Cure-aware editor with LSP support:

1. Open a `.cure` file containing the `|->` operator
2. Hover over any character of the operator
3. Documentation will appear in a tooltip

## Example

```cure
module Example do
  def send_notification(msg: String): Unit =
    msg |-> :notification_server
         ↑ Hover here to see documentation
end
```

## Future Enhancements

The operator detection framework can be extended to provide hover information for other operators:
- `|>` (pipe operator)
- `-->` (FSM transition operator)
- `<$`, `<*>`, `>>=` (functor/applicative/monad operators)

## Files Modified

- `lsp/cure_lsp_analyzer.erl` - Added operator detection and hover support
- `test/lsp_melquiades_hover_test.erl` - New test file
- `docs/lsp-melquiades-operator-support.md` - This documentation

## Date

2025-11-26
