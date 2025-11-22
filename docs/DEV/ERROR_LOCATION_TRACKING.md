# Error Location Tracking in Cure Compiler

This document describes how source location information is tracked and propagated through all stages of the Cure compiler pipeline, ensuring accurate error reporting at every level.

## Overview

Location tracking is critical for providing useful error messages to developers. The Cure compiler maintains location information from lexical analysis through code generation, and even includes mechanisms for runtime error tracing.

## Location Data Structure

All location information uses the `#location{}` record defined in `cure_ast.hrl`:

```erlang
-record(location, {
    line :: integer(),
    column :: integer(),
    file :: string() | undefined
}).
```

## Pipeline Stages

### 1. Lexer (`src/lexer/cure_lexer.erl`)

**Status**: ✅ **Complete**

The lexer tracks line and column for every token and error:

- **Token Location**: Each `#token{}` includes `line` and `column` fields
- **Error Format**: `{error, {Reason, Line, Column}}`
- **Examples**:
  - `{error, {unterminated_string, 5, 12}}`
  - `{error, {unexpected_character, 10, 3}}`

**Key Functions**:
- `scan_quoted_atom/4` - Now properly tracks line numbers (fixed in commit 88d38d6c)
- All scan functions update `Line` and `Column` as they process input

### 2. Parser (`src/parser/cure_parser.erl`)

**Status**: ✅ **Complete**

The parser extracts location from tokens and includes it in all errors:

- **Error Format**: `throw({parse_error, {Reason, ...}, Line, Col})`
- **Location Extraction**: Uses `get_token_line_col/1` and `get_token_line_col_with_state/1`
- **Examples**:
  - `throw({parse_error, {unexpected_token, Type}, Line, Col})`
  - `throw({parse_error, unexpected_end_of_input, Line, Col})`
  - `throw({parse_error, {missing_return_type_for_curify}, Line, Col})`

**Key Improvements** (Commit 0ca04f05):
- Added `last_token` field to `#parser_state{}` for EOF error location
- Fixed 11+ error throwing locations to use actual token positions
- Handles edge cases like EOF using last valid token location

### 3. Type Checker (`src/types/cure_typechecker.erl`)

**Status**: ✅ **Complete**

The type checker uses `Location` field from AST nodes in all errors:

- **Error Format**: `throw({error_type, Reason, Location})`
- **Examples**:
  - `throw({constraint_not_bool, Reason, Location})`
  - `throw({constraint_inference_failed, Reason, Location})`
  - `throw({curify_arity_mismatch, ParamCount, ErlArity, Location})`
  - `throw({missing_return_type_for_curify, Location})`

**AST Node Locations**: All AST expression records include a `location` field that gets passed to error handlers.

### 4. SMT Solver (`src/smt/cure_smt_solver.erl`, `lsp/cure_lsp_smt.erl`)

**Status**: ✅ **Complete**

SMT constraint verification errors include source locations:

- **LSP Integration**: `cure_lsp_smt:verify_refinement_in_body/4` receives `Loc` parameter
- **Error Format**:
  ```erlang
  #{
      location => Loc,
      severity => error,
      message => <<"Refinement type violated for x">>
  }
  ```

**Constraint Extraction**: When extracting constraints from functions, the `location` field from `#function_def{}` is preserved and passed through to diagnostics.

### 5. Code Generation (`src/codegen/`)

**Status**: ✅ **Complete** (Updated in current commit)

Code generation errors now include location information:

**Updated Files**:
- `cure_codegen.erl`:
  - `throw({guard_compilation_failed, Reason, Location})` - Line 1011
  - `throw({guard_compilation_failed, Reason, ClauseLocation})` - Line 1136
  - `throw({curify_arity_mismatch, Name, ActualArity, ErlArity, Location})` - Line 1175

- `cure_beam_compiler.erl`:
  - `throw({clause_compilation_failed, Reason, Loc})` - Line 1010
  - Location extracted from `ClauseInfo` map or defaults to current line

**Error Examples**:
```erlang
% With location
throw({guard_compilation_failed, invalid_expression, #location{line=42, column=10}})

% Arity mismatch with location  
throw({curify_arity_mismatch, foo, 2, 3, #location{line=15, column=5}})
```

### 6. Runtime Errors (`src/runtime/`)

**Status**: ⚠️ **Limited** (By Design)

Runtime errors occur during execution and don't have direct access to source locations. However, Erlang's stack traces provide context:

**Error Context**:
- Function name and arity
- Module name
- Erlang stack trace
- Call chain

**Examples**:
```erlang
throw({lambda_error, Reason})
throw({unsupported_binary_op, Op})
throw(function_call_failed)
```

**Stack Traces**: Erlang automatically captures stack traces that can be correlated back to source:
```erlang
catch error:Reason:Stack ->
    {error, {function_compilation_failed, Name, Reason, Stack}}
```

## LSP Integration (`lsp/cure_lsp_analyzer.erl`)

**Status**: ✅ **Complete**

The LSP server properly converts all error types to diagnostics with locations:

**Location Handling**:
```erlang
make_diagnostic(Message, Line, Column, Severity) ->
    #{
        range => #{
            start => #{line => Line - 1, character => Column - 1},
            end => #{line => Line - 1, character => Column + length(Message)}
        },
        severity => Severity,
        source => <<"cure">>,
        message => list_to_binary(Message)
    }.
```

**Error Type Mapping**:
- **Parser errors**: `{parse_error, Reason, Line, Column}` → Diagnostic
- **Lexer errors**: `{Reason, Line, Column}` → Diagnostic  
- **Type errors**: `#typecheck_error{location=#location{}}` → Diagnostic
- **SMT errors**: `#{location => Loc}` → Diagnostic

**Defensive Handling**: 
- Fallback clauses for malformed errors
- Default locations (0, 0) when location missing
- Guards to prevent crashes on unexpected formats

## Testing Location Tracking

### Lexer Location Test
```bash
erl -pa _build/ebin -s lexer_test run -s init stop
```

**Verified**: ✅ Unterminated strings show correct line/column

### Parser Location Test  
```bash
erl -pa _build/ebin -s parser_test run -s init stop
```

**Verified**: ✅ All parse errors include actual token locations

### LSP Integration Test
**Verified**: ✅ Error diagnostics show at correct positions in editor

### Type Checker Test
```bash
erl -pa _build/ebin -s types_test run -s init stop
```

**Verified**: ✅ Type errors reference source locations from AST

## Best Practices for Maintainers

### When Adding New Errors

1. **Always extract location from AST node**:
   ```erlang
   compile_expr(#some_expr{location = Loc} = Expr, State) ->
       case validate(Expr) of
           {error, Reason} ->
               throw({my_error, Reason, Loc})  % ✅ Include location
       end
   ```

2. **Use token location for parse errors**:
   ```erlang
   {Line, Col} = get_token_line_col(Token),
   throw({parse_error, {reason, Details}, Line, Col})
   ```

3. **Pass location through function calls**:
   ```erlang
   process_function(#function_def{location = Loc} = Func) ->
       helper_function(Func, Loc).  % Pass location to helpers
   ```

4. **Test your errors**:
   - Create intentionally malformed code
   - Verify error points to correct line/column
   - Check LSP shows error at right position

### Common Pitfalls to Avoid

❌ **DON'T** hardcode locations:
```erlang
throw({error, reason, 0, 0})  % BAD!
```

✅ **DO** extract from context:
```erlang
{Line, Col} = get_token_line_col(Token),
throw({error, reason, Line, Col})  % GOOD!
```

❌ **DON'T** lose location in transformations:
```erlang
NewExpr = transform(Expr),  % Lost location!
```

✅ **DO** preserve location fields:
```erlang
NewExpr = transform(Expr),
NewExpr2 = NewExpr#expr{location = Expr#expr.location}  % Preserved!
```

## Commit History

- **88d38d6c**: Fixed lexer quoted atom location tracking
- **0ca04f05**: Fixed 11 parser error locations, added `last_token` tracking
- **aaba4677**: Added defensive LSP error handling
- **Current**: Added location to codegen errors

## Future Improvements

### Potential Enhancements

1. **Enhanced Runtime Tracing**:
   - Embed source location metadata in compiled BEAM modules
   - Use Erlang's line number directives
   - Build source map for better stack traces

2. **Richer Error Context**:
   - Include surrounding code snippet
   - Show expected vs actual at error location
   - Suggest fixes based on error type

3. **Cross-file Location Tracking**:
   - Track import/include file locations
   - Show error chain across module boundaries
   - Link dependent type errors to definition sites

## Summary

✅ **Lexer**: All errors include (Line, Column)  
✅ **Parser**: All errors include (Line, Column) from tokens  
✅ **Type Checker**: All errors include Location from AST  
✅ **SMT Solver**: Constraint errors include source Location  
✅ **Code Generation**: All errors include Location from AST  
⚠️ **Runtime**: Stack traces provide context (no source locations available)  
✅ **LSP Integration**: All error types properly converted to diagnostics

The Cure compiler maintains comprehensive location tracking throughout the compilation pipeline, ensuring developers receive precise, actionable error messages.
