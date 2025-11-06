# Show Typeclass - Quick Reference

## Import

```cure
import Std.Show [Show, show, show_list, show_separated]
```

## Define Custom Instance

### For Simple Records

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
```

### For Generic Types

```cure
record Point(T) do
  x: T
  y: T
end

instance Show(Point(T)) where Show(T) do
  def show(p: Point(T)): String =
    string_concat("Point(",
      string_concat(show(p.x),
        string_concat(", ",
          string_concat(show(p.y), ")"))))
end
```

### For Union Types

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
```

### For Recursive Types

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
```

## Use in Generic Functions

```cure
# Single constraint
def debug(label: String, value: T): T where Show(T) =
  println(string_concat(label, string_concat(": ", show(value))))
  value

# Multiple constraints
def debug_compare(a: T, b: T): String where Show(T), Eq(T) =
  string_concat(show(a), string_concat(" vs ", show(b)))

# With container types
def print_list(items: List(T)): Int where Show(T) =
  println(show_list(items))
  0
```

## Built-in Instances

| Type | Example | Output |
|------|---------|--------|
| `Int` | `show(42)` | `"42"` |
| `Float` | `show(3.14)` | `"3.14"` |
| `String` | `show("hi")` | `"\"hi\""` |
| `Bool` | `show(true)` | `"true"` |
| `Atom` | `show(:ok)` | `"ok"` |
| `List(T)` | `show([1,2,3])` | `"[1, 2, 3]"` |
| `Option(T)` | `show(Some(1))` | `"Some(1)"` |
| `Result(T,E)` | `show(Ok(1))` | `"Ok(1)"` |
| `{T1,T2}` | `show({1,"x"})` | `"{1, \"x\"}"` |

## Helper Functions

```cure
# Custom separator
show_separated([1, 2, 3], " | ")  # => "1 | 2 | 3"

# With parentheses
show_with_parens(42)  # => "(42)"

# Direct list formatting
show_list([1, 2, 3])  # => "[1, 2, 3]"
```

## Common Patterns

### Debug Wrapper

```cure
def debug_value(x: T): T where Show(T) =
  println(show(x))
  x

# Use in pipelines:
result = compute()
  |> debug_value  # Prints intermediate value
  |> transform
```

### Assertion with Context

```cure
def assert_eq(actual: T, expected: T): Result((), String) 
  where Show(T), Eq(T) =
  if eq(actual, expected) then
    Ok(())
  else
    Error(string_concat("Expected ", 
      string_concat(show(expected),
        string_concat(" but got ", show(actual)))))
```

### Logging

```cure
def log_info(msg: String, value: T): T where Show(T) =
  Logger.info(string_concat(msg, show(value)))
  value
```

## Tips

1. **String Concatenation**: Use `string_concat` for building strings
2. **Pattern Matching**: Use `match` for union types
3. **Field Access**: Use dot notation: `person.name`
4. **Constraints**: Add `where Show(T)` when using `show(x)` with generic `T`
5. **Composition**: Show instances compose automatically for nested types

## Common Mistakes

❌ **Forgetting constraint**
```cure
def bad_debug(x: T): T =
  println(show(x))  # ERROR: T must have Show constraint
  x
```

✅ **Adding constraint**
```cure
def good_debug(x: T): T where Show(T) =
  println(show(x))  # OK
  x
```

❌ **Incomplete pattern matching**
```cure
instance Show(Option(T)) where Show(T) do
  def show(opt: Option(T)): String =
    match opt do
      Some(x) -> show(x)
      # ERROR: Missing None case
    end
end
```

✅ **Complete pattern matching**
```cure
instance Show(Option(T)) where Show(T) do
  def show(opt: Option(T)): String =
    match opt do
      Some(x) -> string_concat("Some(", string_concat(show(x), ")"))
      None -> "None"
    end
end
```

## See Also

- Full documentation: `docs/SHOW_TYPECLASS.md`
- Complete examples: `examples/12_show_typeclass.cure`
- Implementation: `lib/std/show.cure`
