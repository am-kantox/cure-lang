# Show Typeclass Implementation

## Overview

This implementation provides a complete, polymorphic `Show` typeclass for the Cure programming language. The `Show` typeclass enables type-safe string conversion for any type that implements it, with automatic composition for container types.

## What's Included

### 1. Standard Library Module (`lib/std/show.cure`)

The core implementation includes:

- **Typeclass Definition**: The `Show(T)` typeclass with a single method `show(x: T): String`
- **Primitive Type Instances**: Built-in instances for `Int`, `Float`, `String`, `Bool`, `Atom`, and `Charlist`
- **Container Type Instances**: Instances for `List(T)`, `Option(T)`, `Result(T, E)`, and tuples (2 and 3 elements)
- **Utility Functions**: Helper functions like `show_list`, `show_separated`, `show_with_parens`
- **FFI Bindings**: Low-level Erlang interop for primitive conversions

### 2. Complete Examples (`examples/12_show_typeclass.cure`)

A comprehensive demonstration showing:

- How to implement `Show` for custom record types
- How to implement `Show` for generic/polymorphic types
- How to implement `Show` for union types (enums)
- How to implement `Show` for recursive data structures
- How to use `Show` constraints in generic functions
- Real-world usage patterns (debug functions, logging, etc.)

### 3. Documentation

#### Full Guide (`docs/SHOW_TYPECLASS.md`)
- Comprehensive tutorial covering all aspects of the `Show` typeclass
- Detailed explanations of typeclass concepts
- Step-by-step implementation guides
- Best practices and design patterns
- Integration examples with other systems

#### Quick Reference (`docs/SHOW_QUICK_REFERENCE.md`)
- Cheat sheet for common patterns
- Quick syntax reference
- Common mistakes and solutions
- Built-in instances table

## Key Features

### 1. **Polymorphic String Conversion**
```cure
def debug(value: T): T where Show(T) =
  println(show(value))
  value

debug(42)                    # Works with Int
debug("hello")               # Works with String
debug([1, 2, 3])            # Works with List
debug(Person{...})          # Works with custom types that implement Show
```

### 2. **Automatic Composition**
Container instances automatically work with any showable element type:
```cure
show([1, 2, 3])                      # => "[1, 2, 3]"
show([Some(1), None, Some(3)])       # => "[Some(1), None, Some(3)]"
show(Ok([{1, "one"}, {2, "two"}]))   # => "Ok([{1, \"one\"}, {2, \"two\"}])"
```

### 3. **Type Safety**
The compiler ensures that only types with `Show` instances can be converted to strings:
```cure
# This won't compile:
def bad_function(x: T): String =
  show(x)  # ERROR: T needs Show constraint

# This will compile:
def good_function(x: T): String where Show(T) =
  show(x)  # OK: constraint ensures T has Show instance
```

### 4. **Extensibility**
Users can easily add `Show` instances for their own types:
```cure
record MyType do
  field: Int
end

instance Show(MyType) do
  def show(x: MyType): String =
    string_concat("MyType(", string_concat(show(x.field), ")"))
end

# Now MyType works everywhere Show is expected
debug(MyType{field: 42})  # Works!
show([MyType{field: 1}, MyType{field: 2}])  # Works!
```

## Usage

### Import the Module

```cure
import Std.Show [Show, show]
```

### Using Built-in Instances

```cure
# All these work out of the box:
show(42)                    # => "42"
show(3.14)                  # => "3.14"
show("hello")               # => "\"hello\""
show(true)                  # => "true"
show([1, 2, 3])            # => "[1, 2, 3]"
show(Some(42))             # => "Some(42)"
show(Ok("success"))        # => "Ok(\"success\")"
show({1, "x", true})       # => "{1, \"x\", true}"
```

### Implementing for Custom Types

```cure
# 1. Define your type
record Person do
  name: String
  age: Int
end

# 2. Implement Show
instance Show(Person) do
  def show(p: Person): String =
    string_concat("Person { name: ",
      string_concat(show(p.name),
        string_concat(", age: ",
          string_concat(show(p.age), " }"))))
end

# 3. Use it!
let alice = Person{name: "Alice", age: 30}
println(show(alice))  # => "Person { name: \"Alice\", age: 30 }"
```

### Writing Generic Functions

```cure
# Any function can require Show with a where clause
def print_values(values: List(T)): Int where Show(T) =
  for value in values do
    println(show(value))
  end
  0
```

## Architecture

### Type System Integration

The implementation leverages Cure's typeclass system (`cure_typeclass.erl`):

1. **Typeclass Registration**: `Show` is registered as a typeclass with its method signature
2. **Instance Registration**: Each instance (e.g., `Show(Int)`) is registered with its implementation
3. **Constraint Checking**: The typechecker verifies that `where Show(T)` constraints are satisfied
4. **Method Resolution**: At compile time, the correct `show` implementation is selected based on type

### Standard Library Organization

```
lib/std/
├── core.cure       # Core types (Option, Result, etc.)
├── show.cure       # Show typeclass (NEW)
└── ...
```

The `Show` module follows the same patterns as other standard library modules, making it feel like a natural part of the language.

## Design Decisions

### 1. String Output Format

The implementation follows Haskell-style conventions:
- Strings are quoted: `"hello"` not `hello`
- Constructors use parentheses: `Some(42)` not `Some 42`
- Lists use brackets: `[1, 2, 3]` not `(1 2 3)`
- Records show field names: `Person { name: "Alice" }` not `Person("Alice")`

### 2. Polymorphic Instances with Constraints

Container instances require their element types to have `Show`:
```cure
instance Show(List(T)) where Show(T) do
  ...
end
```

This ensures that `show([1, 2, 3])` only works if `Int` has a `Show` instance, providing type safety.

### 3. FFI for Primitives

Primitive type conversions use Erlang's built-in functions via FFI:
```cure
curify def int_to_string(x: Int): String = 
  erlang:integer_to_list(x)
```

This provides efficient, well-tested conversions for built-in types.

### 4. Helper Functions

Utility functions like `show_separated` are provided to make common use cases more convenient:
```cure
show_separated([1, 2, 3], " | ")  # => "1 | 2 | 3"
```

## Testing

To test the implementation:

```bash
# Compile the example
cure compile examples/12_show_typeclass.cure

# Run it
cure run examples/12_show_typeclass.cure
```

Expected output demonstrates:
- Primitive type instances
- Container type instances  
- Custom type instances
- Nested structure handling
- Generic function usage

## Future Enhancements

### 1. Automatic Derivation

Support `derive Show` for automatic instance generation:
```cure
record Person do
  name: String
  age: Int
end derive Show
```

This would automatically generate the instance based on the record structure.

### 2. Pretty Printing Support

Add a `Pretty` typeclass for multi-line, indented output:
```cure
typeclass Pretty(T) do
  def pretty(x: T): Doc
end
```

### 3. Custom Formatting

Support format specifiers:
```cure
show_with_format(42, "hexadecimal")  # => "0x2a"
show_with_format(3.14159, "%.2f")    # => "3.14"
```

### 4. Debug vs Display

Separate debug output from user-facing display:
```cure
typeclass Debug(T) do
  def debug(x: T): String  # Developer-focused, verbose
end

typeclass Display(T) do
  def display(x: T): String  # User-facing, concise
end
```

## Related Work

This implementation is inspired by:

- **Haskell's Show**: The original typeclass design and naming conventions
- **Rust's Display/Debug**: Separation of concerns between formats
- **Scala's toString**: Universal string conversion
- **TypeScript's toString**: Practical approach to string conversion

## Contributing

When adding new types to the standard library, remember to:

1. Implement `Show` if the type should be printable
2. Use consistent formatting conventions
3. Add examples to the documentation
4. Test with nested structures

## License

Part of the Cure programming language standard library.

## See Also

- **Documentation**: `docs/SHOW_TYPECLASS.md` - Full guide
- **Quick Reference**: `docs/SHOW_QUICK_REFERENCE.md` - Cheat sheet
- **Examples**: `examples/12_show_typeclass.cure` - Complete working code
- **Implementation**: `lib/std/show.cure` - Source code
- **Typeclass System**: `examples/08_typeclasses.cure` - Basic introduction
