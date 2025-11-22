# Vector Literals in Cure

## Overview

Cure now supports vector literals with a distinct syntax from list literals. This distinction is important for the type system, as vectors have compile-time known lengths while lists do not.

## Syntax

Vector literals use Unicode angle quotation marks:
- **Opening delimiter**: `‹` (U+2039 SINGLE LEFT-POINTING ANGLE QUOTATION MARK)
- **Closing delimiter**: `›` (U+203A SINGLE RIGHT-POINTING ANGLE QUOTATION MARK)

This contrasts with list literals which use square brackets `[]`.

### Examples

```cure
// Empty vector
‹›

// Single element
‹42›

// Multiple elements
‹1, 2, 3›

// Vectors with expressions
‹x + 1, y * 2, z - 3›

// Nested vectors
‹1, ‹2, 3›, ‹4, 5, 6››
```

## Distinction from Lists

| Feature | Lists `[]` | Vectors `‹›` |
|---------|-----------|--------------|
| Length | Runtime-determined | Compile-time known |
| Type | `List(T)` | `Vector(T, n: Nat)` |
| Pattern matching | Cons patterns `[h\|t]` | Fixed-size patterns |
| Use case | Dynamic collections | Fixed-size data |

## Type System Integration

Vectors integrate with Cure's dependent type system:

```cure
// Vector type with length parameter
def safe_access<T>(v: Vector(T, n: Nat), i: Nat): Option(T) 
  when i < n = Some(v[i])

// Type-level guarantees
def first_three<T>(v: Vector(T, n: Nat)): Vector(T, 3)
  when n >= 3 = ‹v[0], v[1], v[2]›
```

## Implementation Details

### Lexer

The lexer recognizes vector delimiters as multi-byte UTF-8 sequences:
- `‹` is encoded as bytes `226, 128, 185` (E2 80 B9)
- `›` is encoded as bytes `226, 128, 186` (E2 80 BA)

These are tokenized as `vector_open` and `vector_close` token types.

### Parser

The parser has a dedicated `parse_vector_literal/1` function that:
1. Expects a `vector_open` token
2. Parses comma-separated expressions
3. Expects a `vector_close` token
4. Returns a `#vector_expr{}` AST node

### AST Representation

```erlang
-record(vector_expr, {
    elements,  % List of expression AST nodes
    location   % Source location
}).
```

## Entering Vector Delimiters

The angle quotation marks can be entered using:

### macOS
- `‹`: Option+Shift+3 or Option+\
- `›`: Option+Shift+4 or Option+Shift+\

### Linux (Compose key)
- `‹`: Compose + < + <
- `›`: Compose + > + >

### Character codes
- `‹`: U+2039 or HTML entity `&lsaquo;`
- `›`: U+203A or HTML entity `&rsaquo;`

### Copy-paste
Simply copy these characters: ‹›

## Testing

Run the vector literal tests:

```bash
make test
erl -pa _build/ebin -s vector_literal_test run -s init stop
```

See `test/vector_literal_test.erl` for comprehensive test cases.

## Example Code

See `examples/vector_demo.cure` for a complete example demonstrating vector literals in various contexts.
