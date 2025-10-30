# Strings in Cure

This document provides comprehensive coverage of string handling in the Cure programming language.

## Table of Contents

1. [Overview](#overview)
2. [String Types](#string-types)
3. [String Literals](#string-literals)
4. [Operations](#operations)
5. [Standard Library](#standard-library)
6. [Unicode Support](#unicode-support)
7. [Pattern Matching](#pattern-matching)
8. [Best Practices](#best-practices)
9. [Interoperability with Erlang](#interoperability-with-erlang)

## Overview

Cure provides first-class support for text processing with three related types:

- **String**: UTF-8 encoded binary (primary string type)
- **Charlist**: List of Unicode codepoints
- **Binary**: Raw byte sequences

This design follows Elixir's approach, providing efficient UTF-8 handling while maintaining compatibility with Erlang's binary and charlist representations.

## String Types

### String

The `String` type represents UTF-8 encoded text stored as a binary.

```cure
name : String
name = "Hello, World!"
```

**Properties:**
- Memory efficient (no overhead per character)
- Fast concatenation with the `<>` operator
- Unicode-aware operations (grapheme iteration by default)
- Direct compatibility with Erlang binaries

**Use when:**
- Working with text data
- Building or parsing text formats
- Storing human-readable strings

### Charlist

The `Charlist` type represents text as a list of Unicode codepoints.

```cure
chars : Charlist
chars = 'Hello, World!'
```

**Properties:**
- Compatible with Erlang's string representation
- Easy list-based manipulation
- Higher memory overhead (8-16 bytes per character)
- Required by some Erlang libraries

**Use when:**
- Interfacing with Erlang code that expects charlists
- Need list-specific operations on individual characters

### Binary

The `Binary` type represents raw byte sequences that may or may not be valid UTF-8.

```cure
data : Binary
data = <<0xFF, 0xFE, 0xFD>>
```

**Use when:**
- Working with binary protocols
- Reading raw file data
- Handling non-UTF-8 encodings

## String Literals

### String Syntax

Strings use straight double quotes (`"`):

```cure
message = "Hello, Cure!"
empty = ""
multiline = "This is a
multi-line string"
```

### Charlist Syntax

Charlists use Unicode curly quotes (`'` and `'` — U+2018 and U+2019):

```cure
erlang_string = 'hello'
atoms = 'atom_compatible'
```

**Note:** Standard ASCII single quotes (`'`) are used for atoms, not charlists.

### Escape Sequences

Both strings and charlists support escape sequences:

```cure
newline = "Hello\nWorld"
tab = "Column1\tColumn2"
quote = "She said \"Hello\""
backslash = "Path\\to\\file"
unicode = "Unicode: \u{1F600}"  % 😀 emoji
```

Supported escape sequences:
- `\n` — newline
- `\r` — carriage return
- `\t` — tab
- `\\` — backslash
- `\"` — double quote
- `\'` — single quote (in charlists)
- `\u{XXXX}` — Unicode codepoint (hexadecimal)

### String Interpolation

(Future feature - planned for Week 2 completion)

```cure
name = "World"
greeting = "Hello, #{name}!"  % => "Hello, World!"

x = 42
message = "The answer is #{x * 2}"  % => "The answer is 84"
```

## Operations

### Concatenation

Use the `<>` operator to concatenate strings:

```cure
hello = "Hello"
world = "World"
greeting = hello <> ", " <> world <> "!"
% => "Hello, World!"
```

The `<>` operator is:
- Right-associative
- Type-checked (only works on String × String → String)
- Optimized by the compiler for multiple concatenations

### Comparison

Strings support all standard comparison operators:

```cure
"apple" == "apple"    % true
"apple" < "banana"    % true (lexicographic)
"abc" <= "abc"        % true
```

### Length and Size

```cure
import String

text = "Hello"
String.length(text)      % => 5 graphemes
String.byte_size(text)   % => 5 bytes

unicode = "世界"
String.length(unicode)      % => 2 graphemes
String.byte_size(unicode)   % => 6 bytes (UTF-8 encoding)
```

## Standard Library

The `String` module provides comprehensive string manipulation functions.

### Conversion Functions

```cure
import String

% String ↔ Charlist
str = "hello"
chars = String.to_charlist(str)      % => [104, 101, 108, 108, 111]
back = String.from_charlist(chars)   % => "hello"

% String ↔ Binary
bin = String.to_binary(str)          % => Same as str (identity)
result = String.from_binary(<<65>>)  % => {ok, "A"}

% String → Atom
atom = String.to_atom("my_atom")     % => :my_atom
```

### Manipulation

```cure
import String

text = "Hello, World!"

% Slicing
String.slice(text, 0, 5)          % => "Hello"
String.slice(text, 7, 5)          % => "World"

% Access by index
String.at(text, 0)                % => {ok, "H"}
String.first(text)                % => {ok, "H"}
String.last(text)                 % => {ok, "!"}

% Splitting
String.split("a,b,c", ",")        % => ["a", "b", "c"]
String.split_at("hello", 3)       % => {"hel", "lo"}
String.lines("line1\nline2")      % => ["line1", "line2"]
String.words("hello world")       % => ["hello", "world"]

% Joining
String.join(["a", "b", "c"], "-") % => "a-b-c"
String.unlines(["a", "b"])        % => "a\nb"
String.unwords(["hello", "world"])% => "hello world"
```

### Trimming and Padding

```cure
import String

padded = "  hello  "
String.trim(padded)               % => "hello"
String.trim_left(padded)          % => "hello  "
String.trim_right(padded)         % => "  hello"

short = "hi"
String.pad_left(short, 5, " ")    % => "   hi"
String.pad_right(short, 5, " ")   % => "hi   "
```

### Case Transformations

```cure
import String

String.upcase("hello")            % => "HELLO"
String.downcase("WORLD")          % => "world"
String.capitalize("cure")         % => "Cure"

% Unicode-aware
String.upcase("café")             % => "CAFÉ"
```

### Predicates

```cure
import String

text = "Hello, World!"

String.starts_with(text, "Hello") % => true
String.ends_with(text, "!")       % => true
String.contains(text, "World")    % => true
String.is_empty("")               % => true
```

### Pattern Matching and Replacement

```cure
import String

String.replace("hello world", "world", "Cure")
% => "hello Cure"

String.replace_all("aaa", "a", "b")
% => "bbb"
```

### Utilities

```cure
import String

String.reverse("hello")           % => "olleh"
String.duplicate("ab", 3)         % => "ababab"
```

## Unicode Support

Cure provides comprehensive Unicode support with grapheme-cluster awareness.

### Graphemes

A **grapheme** is a user-perceived character, which may consist of multiple Unicode codepoints.

```cure
import String

% Simple ASCII
String.graphemes("hello")         % => ["h", "e", "l", "l", "o"]

% Multi-codepoint grapheme (family emoji)
String.graphemes("👨‍👩‍👧‍👦")         % => ["👨‍👩‍👧‍👦"] (single grapheme)

% Accented characters
String.graphemes("café")          % => ["c", "a", "f", "é"]
```

### Codepoints

```cure
import String

String.codepoints("hello")        % => [104, 101, 108, 108, 111]
String.codepoints("世界")          % => [19990, 30028]
```

### UTF-8 Validation

```cure
import String

String.valid_utf8("hello")        % => true
String.valid_utf8(<<0xFF, 0xFF>>) % => false
```

### Default Behavior

All string operations in Cure are **grapheme-aware by default**:

- `String.length/1` returns grapheme count, not byte count
- `String.slice/3` operates on grapheme positions
- `String.at/2` returns graphemes, not bytes
- `String.reverse/1` reverses graphemes, preserving multi-codepoint clusters

## Pattern Matching

### String Prefix Matching

Pattern match on string prefixes using the `<>` operator:

```cure
process_command : String -> Result
process_command(cmd) = case cmd of
    "GET " <> path  -> fetch(path)
    "POST " <> path -> create(path)
    "DELETE " <> path -> remove(path)
    _ -> {error, :unknown_command}
end
```

This compiles to efficient binary pattern matching in Erlang.

### Guard Expressions

String operations in guards:

```cure
is_long_string : String -> Bool when String.length(s) > 100
is_long_string(s) = true

starts_with_http : String -> Bool when String.starts_with(s, "http")
starts_with_http(s) = true
```

## Best Practices

### 1. Prefer Strings Over Charlists

Use `String` (binary) for most text operations:

```cure
% Good
name = "John Doe"

% Avoid (unless needed for Erlang interop)
name = 'John Doe'
```

### 2. Use `<>` for Concatenation

```cure
% Good
full_name = first <> " " <> last

% Avoid
full_name = String.concat(String.concat(first, " "), last)
```

### 3. Build Strings Efficiently

For building large strings, collect parts in a list and join:

```cure
% Good - single allocation
parts = ["Hello", " ", "World", "!"]
result = String.join(parts, "")

% Avoid - multiple allocations
result = "Hello" <> " " <> "World" <> "!"
```

### 4. Use Pattern Matching for Parsing

```cure
% Good
parse_header : String -> {String, String}
parse_header("Content-Type: " <> mime_type) =
    {"Content-Type", mime_type}

% Less idiomatic
parse_header(header) =
    case String.split(header, ": ") of
        [key, value] -> {key, value}
        _ -> {error, :invalid_header}
    end
```

### 5. Validate UTF-8 from External Sources

```cure
% When reading from files, network, etc.
process_input : Binary -> Result String Error
process_input(data) =
    case String.from_binary(data) of
        {ok, str} -> {ok, process_string(str)}
        {error, :invalid_utf8} -> {error, :bad_encoding}
    end
```

## Interoperability with Erlang

### Calling Erlang Functions

Cure strings are Erlang binaries:

```cure
% Direct use with Erlang string module
erlang_string = "hello"
% Erlang: string:uppercase(<<"hello">>)
```

### Charlists for Erlang Libraries

Some Erlang libraries expect charlists:

```cure
import String

% Convert to charlist for Erlang APIs
filename = "/path/to/file"
chars = String.to_charlist(filename)
% Pass `chars` to :file.read_file/1
```

### Binary Pattern Matching

Cure compiles to Erlang binary patterns:

```cure
% Cure
"prefix" <> rest

% Erlang equivalent
<<"prefix", Rest/binary>>
```

## Performance Considerations

### Memory Usage

- **String**: 1 byte per ASCII character, 1-4 bytes per Unicode codepoint
- **Charlist**: 8-16 bytes per character (due to list cell overhead)

### Concatenation

- `<>` operator: O(n) where n = total size
- Multiple concatenations: Use `String.join/2` with a list

### Grapheme Iteration

- Grapheme-aware operations (like `String.length/1`) must iterate the entire string
- Use `String.byte_size/1` when byte count is sufficient

## See Also

- [String Standard Library API](../lib/std/string.cure)
- [Native String Runtime](../src/runtime/cure_string_native.erl)
- [String Examples](../examples/strings/)
- [Editor Setup for Unicode Quotes](EDITOR_SETUP.md)

## Contributing

String implementation improvements are welcome! Key areas:

- Performance optimizations for grapheme operations
- Additional string algorithms (e.g., Levenshtein distance, soundex)
- Locale-aware operations (collation, case folding)
- Regular expression support

See the main [CONTRIBUTING.md](../CONTRIBUTING.md) for details.
