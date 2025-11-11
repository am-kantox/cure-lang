# LSP SMT and Type Checker Integration

This document describes how the Cure Language Server Protocol (LSP) integrates with the type checker and SMT solver to provide real-time verification and feedback.

## Overview

The Cure LSP now includes a comprehensive analysis pipeline that runs on every document change:

1. **Lexical Analysis** - Tokenization
2. **Syntax Parsing** - AST generation
3. **Type Checking** - Dependent type verification
4. **SMT Verification** - Constraint solving and exhaustiveness checking

## Architecture

### Analysis Pipeline

```
Document Change
     ↓
Lexer (cure_lexer)
     ↓
Parser (cure_parser)
     ↓
AST
     ├→ Type Checker (cure_typechecker)
     │       ↓
     │   Type Errors
     │
     └→ SMT Verification (cure_lsp_smt)
             ↓
         SMT Errors (pattern exhaustiveness, refinement violations)
             ↓
     Combined Diagnostics
             ↓
     LSP Client (Editor)
```

### Components

#### 1. Type Checker Integration (`run_type_checker/1`)

The type checker runs on the parsed AST and provides:

- **Dependent type verification**: Validates dependent type constraints
- **Function signature checking**: Ensures parameters and return types match
- **Generic type resolution**: Resolves polymorphic types
- **FSM state verification**: Checks FSM transitions and handlers

**Error Types Detected:**
- Type mismatches
- Undefined variables
- Invalid function calls
- FSM handler signature errors
- Generic type constraint violations

#### 2. SMT Verification Integration (`run_smt_verification/1`)

The SMT solver integration provides:

- **Pattern matching exhaustiveness**: Detects missing match cases
- **Refinement type verification**: Validates type predicates
- **Constraint solving**: Verifies dependent type constraints
- **Counter-example generation**: Provides examples of violations

**Verification Types:**
- Exhaustiveness checking for pattern matches
- Refinement type predicate verification
- Dependent type constraint satisfaction
- Guard condition optimization

## Features

### Real-time Type Checking

As you type, the LSP server:

1. Re-parses the document
2. Runs type checking on the AST
3. Converts type errors to LSP diagnostics
4. Displays errors in the editor

**Example Type Error:**
```cure
def add(x: Int, y: String) -> Int do
    x + y  // Type error: Cannot add Int and String
end
```

The LSP will show:
```
Error: Type mismatch in binary operation '+'
  Expected: Int
  Got: String
```

### Pattern Exhaustiveness Checking

The SMT solver verifies that pattern matches cover all cases:

```cure
def describe(x: Option(Int)) -> String do
    match x do
        | Some(n) -> "Has value"
        // Missing: None case
    end
end
```

The LSP will show:
```
Warning: Pattern match not exhaustive
  Missing case: None
```

### Refinement Type Verification

Validates refinement type predicates:

```cure
type PositiveInt = Int when n > 0

def unsafe_div(x: Int, y: PositiveInt) -> Int do
    x / y  // Safe: y is guaranteed > 0
end
```

If you try to pass a non-positive value:
```cure
unsafe_div(10, -5)  // Error: Refinement type violated
```

### Dependent Type Constraints

Verifies length-indexed types and other dependent constraints:

```cure
def safe_head(xs: List(T, n)) -> T when n > 0 do
    xs[0]  // Safe: length constraint ensures non-empty
end
```

## Implementation Details

### Type Checker Integration

**File**: `src/lsp/cure_lsp_server.erl`

```erlang
run_type_checker(AST) ->
    try
        Env = cure_typechecker:builtin_env(),
        case cure_typechecker:check_module(AST, Env) of
            {ok, _TypedAST, _NewEnv} ->
                [];  % Success
            {error, TypeErrors} ->
                convert_type_errors_to_diagnostics(TypeErrors)
        end
    catch
        _:_ ->
            []  % Don't crash LSP on type checker error
    end.
```

### SMT Verification

**File**: `lsp/cure_lsp_smt.erl`

The SMT verification extracts constraints from the AST:

```erlang
extract_type_constraints(#module_def{items = Items}) ->
    lists:flatmap(fun extract_item_constraints/1, Items).
```

And verifies them:

```erlang
verify_refinement_types(AST) ->
    Constraints = extract_type_constraints(AST),
    lists:filtermap(fun verify_constraint/1, Constraints).
```

### Error Conversion

Type errors and SMT verification results are converted to LSP diagnostics:

```erlang
convert_type_error_to_diagnostic(#typecheck_error{
    message = Message,
    location = #location{line = Line, column = Col}
}) ->
    {true, format_diagnostic(error, Message, Line, Col)}.
```

## Configuration

### Enabling/Disabling Features

You can control which features are enabled via LSP initialization options:

```json
{
  "initializationOptions": {
    "typeChecking": true,
    "smtVerification": true,
    "patternExhaustiveness": true,
    "refinementTypes": true
  }
}
```

### SMT Solver Selection

The SMT backend is auto-detected but can be configured:

```erlang
% In your LSP client config
{solver, z3}       % Use Z3
{solver, cvc5}     % Use CVC5
{solver, symbolic} % Use symbolic evaluation
```

## Performance Considerations

### Caching

The LSP server caches:
- Parsed ASTs (per document version)
- Type environments (per module)
- SMT constraint results (for unchanged code)

### Incremental Analysis

Analysis is incremental:
- Only changed documents are re-analyzed
- Type environments are reused when possible
- SMT queries are cached

### Timeout Protection

Both type checking and SMT verification have timeouts:
- Type checking: 5 seconds
- SMT verification: 5 seconds per constraint

If a timeout occurs, the LSP continues without that analysis.

## Diagnostics

### Severity Levels

- **Error**: Prevents compilation (type mismatches, undefined variables)
- **Warning**: Potential issues (non-exhaustive patterns, unused variables)
- **Info**: Suggestions (type annotations, refactoring hints)
- **Hint**: Style suggestions (naming conventions, simplifications)

### Diagnostic Sources

Each diagnostic includes a source tag:

- `cure-parser`: Parsing errors
- `cure-typecheck`: Type checking errors
- `cure-smt`: SMT verification warnings

## Testing

### Unit Tests

Test the integration with:

```bash
erl -pa _build/ebin -s cure_lsp_server_test run -s init stop
```

### Manual Testing

1. Start the LSP server:
```bash
make lsp_server
```

2. Connect your editor (VS Code, Neovim, etc.)

3. Open a `.cure` file and observe real-time diagnostics

## Future Enhancements

### Planned Features

1. **Code actions**: Auto-fix type errors, add missing pattern cases
2. **Quick fixes**: Suggest type annotations, add imports
3. **Refactoring**: Rename with type awareness, extract function with correct types
4. **Inlay hints**: Show inferred types inline
5. **Semantic highlighting**: Color based on type information

### Optimization Opportunities

1. **Parallel analysis**: Run type checking and SMT in parallel
2. **Incremental SMT**: Only verify changed constraints
3. **Proof caching**: Reuse SMT proofs across compilations
4. **Background processing**: Run expensive checks in background

## Troubleshooting

### Type Checker Not Running

**Symptom**: No type errors shown in editor

**Solutions**:
- Check that `cure_typechecker` module is compiled
- Verify LSP server logs for exceptions
- Ensure `typeChecking: true` in init options

### SMT Verification Slow

**Symptom**: LSP feels sluggish on large files

**Solutions**:
- Reduce SMT timeout in config
- Disable SMT for specific files
- Use symbolic evaluation instead of Z3/CVC5

### False Positives

**Symptom**: Errors shown for valid code

**Solutions**:
- Update type definitions
- Add type annotations to help inference
- Report as a bug with minimal reproduction

## Resources

- [Type System Documentation](../docs/TYPE_SYSTEM.md)
- [SMT Solver Reference](../docs/SMT_QUICK_REFERENCE.md)
- [LSP Features](./LSP_FEATURES.md)
- [Pattern Matching](../docs/PATTERN_MATCHING.md)
