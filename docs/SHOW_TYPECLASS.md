# Show Typeclass - Complete Guide

## Overview

The `Show` typeclass provides a polymorphic interface for converting values to human-readable string representations. It's one of the fundamental typeclasses in Cure's standard library, enabling generic string conversion for any type that implements it.

## Table of Contents

1. [Basic Concepts](#basic-concepts)
2. [Using Show](#using-show)
3. [Built-in Instances](#built-in-instances)
4. [Implementing Show for Custom Types](#implementing-show-for-custom-types)
5. [Polymorphic Instances](#polymorphic-instances)
6. [Utility Functions](#utility-functions)
7. [Advanced Patterns](#advanced-patterns)

## Basic Concepts

### What is a Typeclass?

A typeclass is a language feature that provides ad-hoc polymorphism. It defines a set of functions that can have different implementations depending on the type they operate on. The `Show` typeclass specifically defines how to convert values to strings.

### The Show Typeclass Definition

```cure
typeclass Show(T) do
  def show(x: T): String
end
```

This declares that any type `T` implementing `Show` must provide a `show` function that converts values of type `T` to `String`.

## Using Show

### Importing the Show Module

```cure
import Std.Show [Show, show]
```

This imports:
- The `Show` typeclass definition
- The `show` function (which dispatches to the appropriate instance)

### Basic Usage

```cure
# With primitive types (instances are already defined)
show(42)              # => "42"
show(3.14)            # => "3.14"
show("hello")         # => "\"hello\""
show(true)            # => "true"

# With containers
show([1, 2, 3])       # => "[1, 2, 3]"
show(Some(42))        # => "Some(42)"
show(Ok("success"))   # => "Ok(\"success\")"
```

### Using Show in Generic Functions

The power of `Show` is evident in generic functions:

```cure
# A debug function that works with any showable type
def debug(label: String, value: T): T where Show(T) =
  println(string_concat(label, string_concat(": ", show(value))))
  value

# Usage:
debug("Number", 42)              # Works!
debug("List", [1, 2, 3])         # Works!
debug("Custom", MyRecord{...})   # Works if MyRecord has Show instance!
```

The `where Show(T)` constraint means "this function works for any type `T` that implements `Show`."

## Built-in Instances

The `Std.Show` module provides instances for all primitive and common container types:

### Primitive Types

| Type | Example | Output |
|------|---------|--------|
| `Int` | `show(42)` | `"42"` |
| `Float` | `show(3.14)` | `"3.14"` |
| `String` | `show("hello")` | `"\"hello\""` |
| `Bool` | `show(true)` | `"true"` |
| `Atom` | `show(:example)` | `"example"` |
| `Charlist` | `show('hello')` | `"hello"` |

### Container Types

#### List(T) - where Show(T)

```cure
show([1, 2, 3])           # => "[1, 2, 3]"
show(["a", "b", "c"])     # => "[\"a\", \"b\", \"c\"]"
show([])                  # => "[]"
```

#### Option(T) - where Show(T)

```cure
show(Some(42))            # => "Some(42)"
show(None)                # => "None"
```

#### Result(T, E) - where Show(T), Show(E)

```cure
show(Ok(100))             # => "Ok(100)"
show(Error("failed"))     # => "Error(\"failed\")"
```

#### Tuples - where all elements are showable

```cure
show({1, 2})              # => "{1, 2}"
show({1, "hello", true})  # => "{1, \"hello\", true}"
```

### Nested Structures

Instances compose automatically:

```cure
show([Some(1), None, Some(3)])              # => "[Some(1), None, Some(3)]"
show(Ok([1, 2, 3]))                         # => "Ok([1, 2, 3])"
show([{1, "one"}, {2, "two"}])              # => "[{1, \"one\"}, {2, \"two\"}]"
```

## Implementing Show for Custom Types

### Simple Record Type

```cure
record Person do
  name: String
  age: Int
end

instance Show(Person) do
  def show(p: Person): String =
    string_concat("Person { name: ",
      string_concat(show(p.name),
        string_concat(", age: ",
          string_concat(show(p.age), " }"))))
end

# Usage:
let alice = Person{name: "Alice", age: 30}
show(alice)  # => "Person { name: \"Alice\", age: 30 }"
```

### Union Type (Enum)

```cure
type Color = Red | Green | Blue | RGB(Int, Int, Int)

instance Show(Color) do
  def show(c: Color): String =
    match c do
      Red -> "Red"
      Green -> "Green"
      Blue -> "Blue"
      RGB(r, g, b) ->
        string_concat("RGB(",
          string_concat(show(r),
            string_concat(", ",
              string_concat(show(g),
                string_concat(", ",
                  string_concat(show(b), ")"))))))
    end
end

# Usage:
show(Red)           # => "Red"
show(RGB(255, 0, 0)) # => "RGB(255, 0, 0)"
```

## Polymorphic Instances

### Generic Record Types

For types that are themselves polymorphic, you can create instances with constraints:

```cure
record Point(T) do
  x: T
  y: T
end

# Show instance for Point(T) requires Show(T)
instance Show(Point(T)) where Show(T) do
  def show(p: Point(T)): String =
    string_concat("Point(",
      string_concat(show(p.x),
        string_concat(", ",
          string_concat(show(p.y), ")"))))
end

# Usage - works for any T that has Show:
show(Point{x: 1, y: 2})         # => "Point(1, 2)"
show(Point{x: 1.5, y: 2.5})     # => "Point(1.5, 2.5)"
show(Point{x: "a", y: "b"})     # => "Point(\"a\", \"b\")"
```

### Recursive Data Structures

```cure
type Tree(T) = Leaf | Node(T, Tree(T), Tree(T))

instance Show(Tree(T)) where Show(T) do
  def show(t: Tree(T)): String =
    match t do
      Leaf -> "Leaf"
      Node(value, left, right) ->
        string_concat("Node(",
          string_concat(show(value),
            string_concat(", ",
              string_concat(show(left),
                string_concat(", ",
                  string_concat(show(right), ")"))))))
    end
end

# Usage:
let tree = Node(5, Node(3, Leaf, Leaf), Node(7, Leaf, Leaf))
show(tree)  # => "Node(5, Node(3, Leaf, Leaf), Node(7, Leaf, Leaf))"
```

## Utility Functions

The `Std.Show` module provides several utility functions:

### show_list

Specialized list formatting:

```cure
show_list([1, 2, 3])  # => "[1, 2, 3]"
```

### show_separated

Show list elements with custom separator:

```cure
show_separated([1, 2, 3, 4], " | ")  # => "1 | 2 | 3 | 4"
show_separated(["a", "b", "c"], ", ") # => "a, b, c"
```

### show_with_parens

Wrap string representation in parentheses:

```cure
show_with_parens(42)  # => "(42)"
```

### show_option, show_result, show_tuple

Convenient wrappers for specific types:

```cure
show_option(Some(42))    # => "Some(42)"
show_result(Ok(100))     # => "Ok(100)"
show_tuple({1, 2, 3})    # => "{1, 2, 3}"
```

## Advanced Patterns

### Deriving Show Automatically

In the future, Cure will support automatic derivation:

```cure
record Person do
  name: String
  age: Int
end derive Show

# This will automatically generate the Show instance
```

### Multiple Constraints

Functions can require multiple typeclass constraints:

```cure
def debug_compare(a: T, b: T): String where Show(T), Eq(T) =
  let equal_str = if eq(a, b) then "equal" else "not equal"
  string_concat(show(a),
    string_concat(" and ",
      string_concat(show(b),
        string_concat(" are ", equal_str))))
```

### Show for Wrapper Types

```cure
type UserId = UserId(Int)

instance Show(UserId) do
  def show(uid: UserId): String =
    match uid do
      UserId(id) -> string_concat("UserId(", string_concat(show(id), ")"))
    end
end
```

### Performance Considerations

The `string_concat` function is used extensively. For complex types with many fields, consider:

1. Building intermediate strings and concatenating them
2. Using accumulator patterns for recursive structures
3. Caching string representations for immutable data

```cure
# More efficient for large structures:
def show_complex(x: ComplexType): String =
  let parts = [
    "ComplexType { ",
    "field1: ", show(x.field1), ", ",
    "field2: ", show(x.field2), ", ",
    # ... more fields
    "}"
  ]
  concat_all(parts)  # Single concatenation call
```

## Best Practices

1. **Consistency**: Follow Haskell-style conventions:
   - Constructors with capital letters: `Some(42)`, `Ok(value)`
   - Use parentheses for constructor arguments
   - Use brackets for lists: `[1, 2, 3]`
   - Use braces for records: `Person { name: "Alice" }`

2. **Completeness**: Ensure all cases in sum types are handled:
   ```cure
   instance Show(Result(T, E)) where Show(T), Show(E) do
     def show(result: Result(T, E)): String =
       match result do
         Ok(x) -> ...    # Handle both cases
         Error(e) -> ...
       end
   end
   ```

3. **Polymorphism**: Add constraints only when needed:
   ```cure
   # Good: Only requires Show for the element type
   instance Show(List(T)) where Show(T) do
     ...
   end
   ```

4. **Readability**: Format complex outputs for human consumption:
   ```cure
   # Instead of: "Person(Alice,30,alice@example.com)"
   # Use: "Person { name: \"Alice\", age: 30, email: \"alice@example.com\" }"
   ```

## Integration with Other Systems

### With IO Operations

```cure
import Std.Show [show]
import Std.Io [println]

def display(value: T): Int where Show(T) =
  println(show(value))
  0
```

### With Logging

```cure
def log_debug(value: T): T where Show(T) =
  Logger.debug(show(value))
  value
```

### With Testing

```cure
def assert_eq(actual: T, expected: T): Result((), String) where Show(T), Eq(T) =
  if eq(actual, expected) then
    Ok(())
  else
    Error(string_concat("Expected ",
      string_concat(show(expected),
        string_concat(" but got ", show(actual)))))
```

## Summary

The `Show` typeclass is a foundational abstraction that:

1. **Provides polymorphic string conversion** - one interface, many implementations
2. **Composes automatically** - container instances work for any showable element type
3. **Enables generic programming** - write functions that work with any showable type
4. **Integrates seamlessly** - works with IO, logging, debugging, testing, and more

By implementing `Show` for your custom types and using the constraint `where Show(T)` in your functions, you get powerful, type-safe string formatting that works across your entire codebase.

## See Also

- `examples/12_show_typeclass.cure` - Complete working examples
- `lib/std/show.cure` - Standard library implementation
- `examples/08_typeclasses.cure` - Basic typeclass introduction
- `examples/11_advanced_typeclasses.cure` - Advanced typeclass patterns
