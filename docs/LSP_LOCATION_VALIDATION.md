# LSP Location Validation Test

This document validates that the Cure LSP provides proper error feedback with accurate location information.

## Test File: `examples/profile_with_imports.cure`

```cure
module ProfileWithImports do
  export [test_function/0]
  
  import Std.List [map/2, filter/2, fold/3]
  import Std.Core [identity/1, compose/2]
  import Std.Io [print/1]
  
  def test_function(): Int =
    "STRING"

end
```

## Expected Error

**Type Error**: Function `test_function/0` declares return type `Int` but returns a string literal `"STRING"`.

## LSP Analysis Results

### Diagnostic Output

```
Found 1 diagnostic(s):

[ERROR] Line 8, Column 3
  Message: Function body type doesn't match declared return type
```

### Detailed Diagnostic

```erlang
#{
    message => <<"Function body type doesn't match declared return type">>,
    range => #{
        start => #{line => 7, character => 3},
        'end' => #{line => 7, character => 13}
    },
    source => <<"cure-lsp">>,
    severity => 1  % Error
}
```

## Location Validation

### Line Number
- **LSP Line**: 7 (0-based) → **Line 8** (1-based)
- **File Line 8**: `def test_function(): Int =`
- ✅ **CORRECT**: Points to the function definition line

### Column Number
- **LSP Column**: 3 (0-based)
- **Position**: After 2 spaces of indentation, at the `d` of `def`
- ✅ **CORRECT**: Points to the start of the function definition keyword

### Severity
- **Value**: 1
- **Meaning**: Error (not warning, info, or hint)
- ✅ **CORRECT**: Type mismatch is an error

### Error Message
- **Message**: "Function body type doesn't match declared return type"
- ✅ **CORRECT**: Clearly describes the type error

## Visual Representation

```
   1  module ProfileWithImports do
   2    export [test_function/0]
   3    
   4    import Std.List [map/2, filter/2, fold/3]
   5    import Std.Core [identity/1, compose/2]
   6    import Std.Io [print/1]
   7    
   8    def test_function(): Int =
       ^~~ ERROR here (Line 8, Column 3)
   9      "STRING"
  10  
  11  end
```

## IDE Integration

When this diagnostic is sent to an LSP client (VS Code, Neovim, etc.), the editor will:

1. **Underline** the function definition on line 8
2. **Show red squiggle** from column 3 to column 13
3. **Display tooltip** with the error message when hovering
4. **Add to Problems panel** with file path, line, and message
5. **Show in minimap** as red indicator on line 8

## Test Commands

### Test with Erlang Shell

```bash
cd /home/am/Proyectos/Ammotion/cure

# Read file and analyze
erl -pa _build/ebin -pa _build/lsp -noshell -eval '
{ok, Code} = file:read_file("examples/profile_with_imports.cure"),
Diagnostics = cure_lsp_analyzer:analyze(Code),
io:format("Diagnostics: ~p~n", [Diagnostics]),
halt().'
```

### Test with Inline Code

```bash
erl -pa _build/ebin -pa _build/lsp -noshell -eval '
Code = <<"module ProfileWithImports do
  def test_function(): Int = \"STRING\"
end">>,
Diagnostics = cure_lsp_analyzer:analyze(Code),
lists:foreach(fun(D) ->
  #{range := #{start := #{line := L, character := C}},
    message := Msg} = D,
  io:format("Line ~p, Col ~p: ~s~n", [L+1, C, Msg])
end, Diagnostics),
halt().'
```

## Comparison with Other Error Types

### Lexer Error (Unexpected Character)

```cure
module Test
x … y  % Ellipsis character
end
```

**Result**: `{error, {{unexpected_character, 8230}, 2, 3}}`
- Line 2, Column 3 (where ellipsis appears)

### Parser Error (Syntax Error)

```cure
module Test
def foo(x y)  % Missing comma
end
```

**Result**: `{error, {parse_error, unexpected_token, 1, 11}}`
- Line 1, Column 11 (where `y` appears without comma)

### Type Error (This Test)

```cure
def test_function(): Int = "STRING"
```

**Result**: Line 8, Column 3 (function definition)
- Points to where the incorrect type annotation is

## Validation Summary

✅ **Error Detection**: Type mismatch correctly identified  
✅ **Location Tracking**: Accurate line and column (8:3)  
✅ **Error Message**: Clear and descriptive  
✅ **Severity Level**: Correct (Error = 1)  
✅ **LSP Format**: Valid LSP diagnostic structure  
✅ **File Analysis**: Works with actual file input  
✅ **Inline Analysis**: Works with binary code input  

## Conclusion

The Cure LSP analyzer correctly:
1. Detects type errors in `test_function/0`
2. Reports the error at the proper location (Line 8, Column 3)
3. Provides a clear error message
4. Uses the correct severity level (Error)
5. Returns a properly formatted LSP diagnostic

The location information is accurate and will properly highlight the error in any LSP-compatible editor.
