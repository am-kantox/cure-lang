# Lexer Error Format

This document describes the error format returned by the Cure lexer, including location information for all errors.

## Error Format

All lexer errors are returned in the following format:

```erlang
{error, {Reason, Line, Column}}
```

Where:
- `Reason` - Error reason (atom or tuple describing the error)
- `Line` - Line number where error occurred (1-based integer)
- `Column` - Column number where error occurred (1-based integer)

## Error Types

### Unexpected Character

When an unrecognized character is encountered:

```erlang
{error, {{unexpected_character, CodePoint}, Line, Column}}
```

- `CodePoint` - Unicode codepoint of the unexpected character (integer)

**Example**:
```erlang
cure_lexer:tokenize(<<"test … fail">>).
% => {error, {{unexpected_character, 8230}, 1, 6}}
% 8230 = U+2026 (horizontal ellipsis)
```

### Invalid UTF-8

When malformed UTF-8 is encountered:

```erlang
{error, {{invalid_utf8, FirstByte}, Line, Column}}
```

- `FirstByte` - The first byte of the invalid sequence

### Unterminated String

When a string literal is not closed:

```erlang
{error, {unterminated_string, Line, Column}}
```

**Example**:
```erlang
cure_lexer:tokenize(<<"x = \"hello">>).
% => {error, {unterminated_string, 1, 13}}
```

### Unterminated Quoted Atom

When a quoted atom is not closed:

```erlang
{error, {unterminated_quoted_atom, Line, Column}}
```

### Unterminated Interpolation

When string interpolation `#{...}` is not properly closed:

```erlang
{error, {unterminated_interpolation, Line, Column}}
```

### Unterminated Charlist

When a charlist literal (using Unicode quotes) is not closed:

```erlang
{error, {{unterminated_charlist, Line, Column}}}
```

## Location Tracking

### Line Numbers
- 1-based indexing
- Incremented on every newline character (`\n`)
- Reset column to 1 after newline

### Column Numbers
- 1-based indexing
- Incremented for each character processed
- Multi-byte UTF-8 characters count as 1 column
- Reset to 1 at the start of each line

### Example with Multi-line Code

```erlang
Code = <<"line 1
line 2
x … y
line 4">>.

cure_lexer:tokenize(Code).
% => {error, {{unexpected_character, 8230}, 3, 3}}
%    Line 3 (third line)
%    Column 3 (after "x ")
```

## UTF-8 Support

The lexer properly handles UTF-8 characters in error reporting:

### 1-byte (ASCII)
```erlang
cure_lexer:tokenize(<<"x $ y">>).
% => {error, {{unexpected_character, 36}, 1, 3}}
% 36 = U+0024 ($)
```

### 2-byte UTF-8
```erlang
cure_lexer:tokenize(<<"x ¢ y">>).
% => {error, {{unexpected_character, 162}, 1, 3}}
% 162 = U+00A2 (¢)
```

### 3-byte UTF-8
```erlang
cure_lexer:tokenize(<<"x … y">>).
% => {error, {{unexpected_character, 8230}, 1, 3}}
% 8230 = U+2026 (…)
```

### 4-byte UTF-8 (Emoji)
```erlang
cure_lexer:tokenize(<<"x 😀 y">>).
% => {error, {{unexpected_character, 128512}, 1, 3}}
% 128512 = U+1F600 (😀)
```

## Integration with LSP

The LSP server uses the location information to create diagnostics with proper ranges:

```erlang
% Lexer error
{error, {{unexpected_character, 8230}, 3, 6}}

% Converted to LSP diagnostic
#{
    range => #{
        start => #{line => 2, character => 5},  % 0-based in LSP
        end => #{line => 2, character => 6}
    },
    severity => 1,  % Error
    source => <<"cure">>,
    message => <<"Unexpected character: … (U+2026)">>
}
```

## Testing Location Tracking

To verify location tracking:

```erlang
% Test line tracking
cure_lexer:tokenize(<<"a\nb\nc … d">>).
% => {error, {{unexpected_character, 8230}, 3, 3}}

% Test column tracking  
cure_lexer:tokenize(<<"hello … world">>).
% => {error, {{unexpected_character, 8230}, 1, 7}}

% Test multi-byte at column 1
cure_lexer:tokenize(<<"…test">>).
% => {error, {{unexpected_character, 8230}, 1, 1}}
```

## Summary

✅ **All lexer errors include location information**  
✅ **Line and column are 1-based**  
✅ **UTF-8 characters properly decoded to codepoints**  
✅ **Location tracking accurate across newlines**  
✅ **Multi-byte UTF-8 counted as single column**  
✅ **LSP integration uses location for diagnostics**

The Cure lexer provides comprehensive location information for all errors, enabling precise error reporting in both command-line and IDE environments.
