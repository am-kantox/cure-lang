# LSP Diagnostic Update Fix

## Problem

The Cure LSP was not updating diagnostics when code changed in the editor. When you modified code to fix an error, the editor would continue showing the old error message indefinitely (e.g., `cure-lsp: {unexpected_token, identifier}`).

## Root Cause

The issue had multiple contributing factors:

### 1. **Sync Mode Mismatch**
- The LSP advertised support for **incremental sync** (mode 2) in the `initialize` response
- However, the `apply_single_change/2` function only handled **full document sync** (mode 1)
- When the editor sent incremental changes with `range` fields, the LSP couldn't apply them correctly

### 2. **Silent Failures**
- When `apply_changes/2` failed, there was no error handling
- Failed document updates would leave stale content in the LSP state
- Diagnostics would continue to analyze old content

### 3. **Missing Error Recovery**
- If analysis crashed or failed, no diagnostics would be sent
- The editor would keep showing old diagnostics forever

## Solution

### Changes Made to `lsp/cure_lsp.erl`

#### 1. Changed to Full Document Sync (Simpler & More Reliable)

**Line 257** - Changed sync mode from 2 (incremental) to 1 (full):

```erlang
% Before:
change => 2,  % Incremental

% After:
change => 1,  % Full document sync (mode 1) - simpler and more reliable
```

This means the editor sends the **entire document content** on every change, which is simpler to implement correctly.

#### 2. Enhanced `apply_single_change/2` to Handle Both Modes

**Lines 489-546** - Added support for both full and incremental sync:

```erlang
apply_single_change(Change, Text) ->
    case maps:get(range, Change, undefined) of
        undefined ->
            % Full document replacement (mode 1)
            maps:get(text, Change, Text);
        Range ->
            % Incremental change (mode 2) - apply range-based edit
            StartPos = maps:get(start, Range),
            EndPos = maps:get('end', Range),
            NewText = maps:get(text, Change, <<>>),
            apply_range_change(Text, StartPos, EndPos, NewText)
    end.
```

This handles both sync modes, making the LSP robust to different editor configurations.

#### 3. Added Comprehensive Error Handling in `handle_did_change/2`

**Lines 323-378** - Added error handling and debug logging:

```erlang
handle_did_change(Params, State) ->
    ...
    io:format(standard_error, "[LSP] Document changed: ~s (version ~p)~n", [Uri, Version]),
    
    case maps:get(Uri, State#state.documents, undefined) of
        undefined ->
            % Treat as new document if not found
            handle_did_open(...);
        Doc ->
            % Apply changes with error recovery
            NewText =
                try
                    apply_changes(OldText, ContentChanges)
                catch
                    Error:Reason:Stack ->
                        io:format(standard_error, "[LSP] Error applying changes: ~p:~p~n", 
                                 [Error, Reason]),
                        % Fall back to full text from changes
                        get_text_from_changes(ContentChanges)
                end,
            
            % Run diagnostics with error handling
            try
                diagnose_document(Uri, NewText, NewState),
                io:format(standard_error, "[LSP] Diagnostics sent~n")
            catch
                _:DiagErr:DiagStack ->
                    io:format(standard_error, "[LSP] Diagnostic error: ~p~n", [DiagErr]),
                    % Send empty diagnostics on error to clear stale ones
                    send_empty_diagnostics(Uri, NewState)
            end,
            ...
    end.
```

Key improvements:
- **Debug logging** at every step
- **Fallback to full text** if incremental application fails
- **Empty diagnostics sent** on analysis errors to clear stale diagnostics
- **Document not found** treated as new document

#### 4. Added Helper Functions

**Lines 593-609** - New helper functions:

```erlang
send_empty_diagnostics(Uri, State) ->
    % Send empty diagnostic list to clear errors in editor
    ...

get_text_from_changes([Change | _]) ->
    % Extract full text from changes (for full document sync)
    maps:get(text, Change, <<>>).
```

## Testing

### Command-Line Testing

1. **Build the LSP**:
   ```bash
   cd /home/am/Proyectos/Ammotion/cure
   make lsp
   ```

2. **Test analyzer updates**:
   ```bash
   erl -pa _build/ebin -pa _build/lsp -noshell -eval '
   Code1 = <<"module Test do\n  def foo() = 42\nend">>,
   Diag1 = cure_lsp_analyzer:analyze(Code1),
   io:format("Valid code diagnostics: ~p~n", [length(Diag1)]),
   
   Code2 = <<"module Test do\n  def foo( x y) = 42\nend">>,
   Diag2 = cure_lsp_analyzer:analyze(Code2),
   io:format("Broken code diagnostics: ~p~n", [length(Diag2)]),
   halt().'
   ```

   Expected output:
   ```
   Valid code diagnostics: 0
   Broken code diagnostics: 1
   ```

### Editor Testing

#### Prerequisites

1. **Restart the LSP server** after rebuilding:
   - In Neovim: `:LspRestart`
   - In VS Code: Reload window (Ctrl+Shift+P → "Developer: Reload Window")
   - Or restart your editor

2. **Enable LSP logging** (optional but helpful):
   ```bash
   # Redirect LSP stderr to a log file in your editor config
   # Neovim example:
   cmd = { "cure-lsp" },
   handlers = {
     ["$/logMessage"] = function(_, result, ctx)
       print(result.message)
     end,
   },
   ```

#### Test Procedure

1. **Open a Cure file** with a syntax error:
   ```cure
   module Test do
     def foo( x y) = 42  % Missing comma - syntax error
   end
   ```

2. **Verify error appears**:
   - You should see a diagnostic highlighting the syntax error
   - Hover over the error to see: `{unexpected_token, identifier}`

3. **Fix the error**:
   ```cure
   module Test do
     def foo(x, y) = 42  % Fixed: added comma
   end
   ```

4. **Save the file** (or wait for auto-save)

5. **Verify diagnostic clears**:
   - The error should disappear within 1-2 seconds
   - No red squiggles should remain

6. **Test with type error**:
   ```cure
   module Test do
     def bar(): Int = "string"  % Type error
   end
   ```

7. **Fix the type error**:
   ```cure
   module Test do
     def bar(): Int = 42  % Fixed
   end
   ```

8. **Verify type error clears**

#### Debug LSP Issues

If diagnostics still don't update:

1. **Check LSP is running**:
   ```bash
   ps aux | grep cure-lsp
   ```

2. **Check stderr output** (if you configured logging):
   ```bash
   tail -f /tmp/cure-lsp.log
   ```

   You should see:
   ```
   [LSP] Document changed: file:///path/to/file.cure (version 2)
   [LSP] Text updated, length: 123 bytes
   [LSP] Diagnostics sent for file:///path/to/file.cure
   ```

3. **Test analyzer directly**:
   ```bash
   erl -pa _build/ebin -pa _build/lsp
   ```
   ```erlang
   1> Code = <<"module Test do\n  def foo() = 42\nend">>.
   2> Diag = cure_lsp_analyzer:analyze(Code).
   3> length(Diag).
   0
   ```

4. **Restart LSP server** if needed

## Technical Details

### LSP Document Sync Modes

LSP supports two document synchronization modes:

1. **Full Document Sync (mode 1)**:
   - Editor sends **entire document content** on every change
   - Simpler to implement
   - Slightly higher bandwidth but negligible for typical files

2. **Incremental Sync (mode 2)**:
   - Editor sends only **changed ranges** with start/end positions
   - More efficient for large files
   - More complex to implement correctly (need to handle multi-line edits, UTF-8, etc.)

We chose mode 1 for reliability. For typical Cure files (<10KB), the performance difference is negligible.

### Error Recovery Strategy

The fix implements a three-level error recovery strategy:

1. **Primary Path**: Normal operation with full error handling
2. **Fallback**: Extract full text from changes if incremental application fails
3. **Last Resort**: Send empty diagnostics to clear stale errors if analysis crashes

This ensures the LSP never gets stuck in a bad state.

## Verification

Run the provided test script:

```bash
./test_lsp_changes.sh
```

Expected output:
```
Testing LSP diagnostic updates...
==================================

Test 1: Verify cure_lsp_analyzer can handle code changes
----------------------------------------------------------
Analyzing broken code...
Diagnostics: 1

Analyzing fixed code...
Diagnostics: 0

✓ Analyzer correctly detects and clears errors

Test 2: Check that analyzer handles type errors
------------------------------------------------
Analyzing type error code...
Diagnostics count: 1
  - Function body type doesn't match declared return type

Analyzing fixed type...
Diagnostics count: 0

✓ Analyzer correctly handles type error transitions

==================================
LSP diagnostic update tests complete
```

## Files Modified

1. `lsp/cure_lsp.erl`:
   - Lines 254-258: Changed to full document sync
   - Lines 323-378: Enhanced error handling in `handle_did_change/2`
   - Lines 486-546: Improved `apply_single_change/2` with range support
   - Lines 593-609: Added helper functions

## Commit Message

```
Fix LSP diagnostic updates on document changes

- Change from incremental sync (mode 2) to full document sync (mode 1) for reliability
- Add comprehensive error handling in document change handler
- Implement fallback to full text extraction if change application fails
- Send empty diagnostics on analysis errors to clear stale diagnostics
- Add debug logging for easier troubleshooting

This fixes the issue where diagnostics would get stuck with old errors
after the code was fixed in the editor.
```
