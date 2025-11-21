# Make LSP Fix

## Problem
Running `make lsp` was failing with compilation errors because it was attempting to compile test and script files as regular Erlang modules:

```
lsp/test_code_actions.erl:1:1: syntax error before: '#'
  Line 1: #!/usr/bin/env escript
lsp/test_code_actions.erl:5:2: no module definition
  Line 5: -mode(compile).
```

## Root Cause
The `LSP_SRC` variable in the Makefile was using a wildcard pattern that included ALL `.erl` files in the `lsp/` directory:

```makefile
LSP_SRC = $(wildcard $(LSP_DIR)/*.erl)
```

This included:
- `test_code_actions.erl` - An escript (executable script), not a regular module
- `test_analyzer.erl` - Test module
- `test_cure_lsp_comprehensive.erl` - Test module

Escript files start with `#!/usr/bin/env escript` and use `-mode(compile).` which are not valid for regular Erlang module compilation.

## Solution
Modified the `LSP_SRC` definition to filter out test files:

```makefile
# Before
LSP_SRC = $(wildcard $(LSP_DIR)/*.erl)

# After
LSP_SRC = $(filter-out $(LSP_DIR)/test_%.erl $(LSP_DIR)/%_test.erl, $(wildcard $(LSP_DIR)/*.erl))
```

This filters out:
- Files starting with `test_` (e.g., `test_code_actions.erl`, `test_analyzer.erl`)
- Files ending with `_test.erl` (e.g., `*_test.erl`)

## Files Modified
- `/opt/Proyectos/Ammotion/cure/Makefile` (line 28)

## Verification

### Before Fix
```bash
$ make lsp
lsp/test_code_actions.erl:1:1: syntax error before: '#'
make: *** [Makefile:164: _build/lsp/test_code_actions.beam] Error 1
```

### After Fix
```bash
$ make lsp
Compiling LSP lsp/cure_lsp_analyzer.erl...
Compiling LSP lsp/cure_lsp_document.erl...
Compiling LSP lsp/cure_lsp_enhanced.erl...
Compiling LSP lsp/cure_lsp.erl...
Compiling LSP lsp/cure_lsp_profiler.erl...
Compiling LSP lsp/cure_lsp_smt.erl...
Compiling LSP lsp/cure_lsp_symbols.erl...
Compiling LSP lsp/cure_lsp_type_holes.erl...
Creating LSP executable scripts...
LSP scripts are now executable
Cure LSP server built successfully
```

### Compiled Modules
```bash
$ ls -1 _build/lsp/*.beam
_build/lsp/cure_lsp.beam
_build/lsp/cure_lsp_analyzer.beam
_build/lsp/cure_lsp_document.beam
_build/lsp/cure_lsp_enhanced.beam
_build/lsp/cure_lsp_profiler.beam
_build/lsp/cure_lsp_smt.beam
_build/lsp/cure_lsp_symbols.beam
_build/lsp/cure_lsp_type_holes.beam
```

All 8 production LSP modules compiled successfully, with no test files included.

### Full Build Test
```bash
$ make clean && make all && make lsp
# Completes successfully with exit code 0
```

## LSP Script Configuration
The `cure-lsp` script correctly references the compiled modules:

```erlang
Paths = [
  filename:join(ScriptDir, "_build/ebin"),      % Core compiler modules
  filename:join(ScriptDir, "_build/lsp"),       % LSP modules
  filename:join(ScriptDir, "_build/lib"),       % Standard library
  filename:join(ScriptDir, "_build/lib/std")
],
```

## Testing LSP
```bash
$ ./cure-lsp --version
Cure Language Server version 0.1.0

$ ./cure-lsp --help
Cure Language Server Protocol Implementation

Usage:
  cure-lsp [start]     Start the LSP server (default)
  cure-lsp --version   Show version information
  cure-lsp --help      Show this help message

The server communicates via stdin/stdout using the Language Server Protocol.
```

## Test Files
Test files remain available for manual testing but are not included in the production build:
- `lsp/test_code_actions.erl` - Test type hole code actions
- `lsp/test_analyzer.erl` - Test analyzer functionality  
- `lsp/test_cure_lsp_comprehensive.erl` - Comprehensive LSP tests

These can be run manually using escript:
```bash
$ cd lsp
$ ./test_code_actions.erl
```

## Related Work
This fix was part of the larger type hole code action implementation, which also included:
- Fixing diagnostic location tracking (see `LSP_TYPE_HOLE_CODE_ACTION_FIX.md`)
- Implementing type inference for remote calls
- Full LSP integration for code actions
