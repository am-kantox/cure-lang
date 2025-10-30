# String Examples for Cure

This directory contains example programs demonstrating string handling in Cure.

## Examples

### 01_basics.cure

Demonstrates fundamental string operations:
- String literals and concatenation with `<>`
- String properties (length, byte size, emptiness)
- Case transformations (upcase, downcase, capitalize)
- String predicates (starts_with, ends_with, contains)

**Run:** `cure run 01_basics.cure`

### 02_unicode.cure

Shows Unicode-aware string handling:
- Grapheme-level operations
- Multilingual text (English, Spanish, French, German, Japanese, Chinese, Arabic, Russian)
- Emoji handling and detection
- Codepoint analysis and ranges
- Unicode normalization checks
- Case-insensitive comparisons

**Run:** `cure run 02_unicode.cure`

### 03_pattern_matching.cure

Demonstrates pattern matching on strings:
- HTTP request parsing (GET, POST, PUT, DELETE, PATCH)
- URL protocol detection (http, https, ftp, ws, wss)
- File extension processing and MIME type detection
- Command-line flag parsing
- Email validation (simplified)
- Path operations (absolute/relative, joining)
- Prefix and suffix stripping
- Configuration file parsing (key-value pairs, comment filtering)

**Run:** `cure run 03_pattern_matching.cure`

## Key Concepts

### String Types

Cure has three related string types:

- **String**: UTF-8 encoded binary (primary type)
- **Charlist**: List of Unicode codepoints
- **Binary**: Raw byte sequences

Use `String` for most operations. Use `Charlist` when interfacing with Erlang libraries that require it.

### Literal Syntax

```cure
str = "Hello"          % String (straight double quotes)
chars = 'Hello'        % Charlist (Unicode curly quotes U+2018/U+2019)
atom = 'hello'         % Atom (ASCII single quote)
```

### Concatenation

```cure
greeting = "Hello" <> ", " <> "World!"
```

The `<>` operator is right-associative and type-safe (String × String → String).

### Pattern Matching

```cure
process(request) = case request of
    "GET " <> path -> handle_get(path)
    "POST " <> path -> handle_post(path)
    _ -> error("Unknown method")
end
```

### Unicode Awareness

All string operations are grapheme-aware by default:

```cure
String.length("hello")     % => 5
String.length("café")      % => 4 (graphemes, not bytes)
String.length("👨‍👩‍👧‍👦")     % => 1 (family emoji is single grapheme)
```

## Common Patterns

### Building Strings Efficiently

```cure
% Good: collect parts, then join
parts = ["Error: ", message, " at line ", line_num]
error_msg = String.join(parts, "")

% Less efficient: multiple concatenations
error_msg = "Error: " <> message <> " at line " <> line_num
```

### Processing Lines

```cure
process_file(content) =
    let
        lines = String.lines(content)
        filtered = List.filter(is_not_empty, lines)
        processed = List.map(process_line, filtered)
    in
        String.unlines(processed)
```

### Case-Insensitive Comparison

```cure
equal_ignore_case(a, b) =
    String.downcase(a) == String.downcase(b)
```

## See Also

- [String Documentation](../../docs/STRINGS.md) - Comprehensive guide
- [String Standard Library](../../lib/std/string.cure) - Full API
- [Editor Setup](../../docs/EDITOR_SETUP.md) - Configure Unicode quote input

## Contributing

Have an interesting string processing example? Feel free to add it to this directory!

Format:
1. Create a `.cure` file with a descriptive name
2. Add clear comments explaining the concepts
3. Include a `demo()` function showing usage
4. Update this README with a description

See [CONTRIBUTING.md](../../CONTRIBUTING.md) for guidelines.
