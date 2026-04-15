%{
  title: "Protocols",
  description: "Ad-hoc polymorphism via proto/impl with guard-based dispatch.",
  order: 5
}
---

Protocols are Cure's mechanism for ad-hoc polymorphism. They define a set of
functions that can have different implementations for different types, all
resolved at compile time into guard-dispatched BEAM functions.

## Defining a protocol

A protocol declares a type parameter and one or more function signatures:

```cure
proto Show(T)
  fn show(x: T) -> String
```

`T` is a type variable. Each implementation substitutes a concrete type for `T`.

A protocol can declare multiple methods:

```cure
proto Collection(C)
  fn size(c: C) -> Int
  fn is_empty(c: C) -> Bool
```

## Implementing a protocol

Use `impl` to provide a concrete implementation for a specific type:

```cure
impl Show for Int
  fn show(x: Int) -> String = Std.String.from_int(x)

impl Show for Float
  fn show(x: Float) -> String = Std.String.from_float(x)

impl Show for String
  fn show(x: String) -> String = "\"" <> x <> "\""

impl Show for Bool
  fn show(x: Bool) -> String = if x then "true" else "false"

impl Show for Atom
  fn show(x: Atom) -> String = ":" <> Std.String.from_atom(x)
```

The function body inside an `impl` block has the same syntax as any other
function. You can use pattern matching, guards, `let` bindings, and call
other functions.

## How dispatch works: guard compilation

The compiler does not generate vtables or dictionary lookups. Instead, it
compiles each protocol method into a multi-clause BEAM function with
Erlang guard tests.

Given the `Show` protocol above, the codegen produces roughly:

```erlang
show(X) when is_integer(X)  -> show__for__int(X);
show(X) when is_boolean(X)  -> show__for__bool(X);
show(X) when is_float(X)    -> show__for__float(X);
show(X) when is_binary(X)   -> show__for__string(X);
show(X) when is_atom(X)     -> show__for__atom(X).
```

Each `show__for__<type>` is a private function containing the implementation
body. The dispatch function is exported.

The guard mapping is:

- `Int` -> `is_integer`
- `Float` -> `is_float`
- `String` -> `is_binary`
- `Bool` -> `is_boolean`
- `Atom` -> `is_atom`
- `List` -> `is_list`
- `Tuple` -> `is_tuple`
- `Map` -> `is_map`
- `Pid` -> `is_pid`
- `Ref` -> `is_reference`

## Clause ordering by type specificity

On the BEAM, `true` and `false` are atoms. That means `is_atom(true)` returns
`true`. If the `Atom` clause came before the `Bool` clause, boolean values
would dispatch to the wrong implementation.

The compiler sorts clauses by type specificity:

- `Bool` has specificity 0 (checked first)
- `Int`, `Float`, `String`, `List`, `Tuple`, `Map`, `Pid`, `Ref` have specificity 1
- `Atom` has specificity 10 (checked last among primitives)

This ordering is automatic. You never need to worry about the order in which
you write `impl` blocks.

## The Eq protocol

```cure
mod Std.Eq
  proto Eq(T)
    fn eq(a: T, b: T) -> Bool

  impl Eq for Int
    fn eq(a: Int, b: Int) -> Bool = a == b

  impl Eq for Float
    fn eq(a: Float, b: Float) -> Bool = a == b

  impl Eq for String
    fn eq(a: String, b: String) -> Bool = a == b

  impl Eq for Bool
    fn eq(a: Bool, b: Bool) -> Bool = a == b

  impl Eq for Atom
    fn eq(a: Atom, b: Atom) -> Bool = a == b

  fn ne(a: T, b: T) -> Bool = if eq(a, b) then false else true
```

The `ne` function is not part of the protocol declaration -- it's a regular
function that calls the dispatched `eq`. Any module can define helper functions
alongside protocol definitions.

## The Ord protocol

```cure
mod Std.Ord
  proto Ord(T)
    fn compare(a: T, b: T) -> Atom

  impl Ord for Int
    fn compare(a: Int, b: Int) -> Atom =
      if a < b then :lt else if a > b then :gt else :eq

  impl Ord for Float
    fn compare(a: Float, b: Float) -> Atom =
      if a < b then :lt else if a > b then :gt else :eq

  impl Ord for String
    fn compare(a: String, b: String) -> Atom =
      if a < b then :lt else if a > b then :gt else :eq

  impl Ord for Atom
    fn compare(a: Atom, b: Atom) -> Atom =
      if a < b then :lt else if a > b then :gt else :eq

  fn lt(a: T, b: T) -> Bool = compare(a, b) == :lt
  fn le(a: T, b: T) -> Bool = compare(a, b) != :gt
  fn gt(a: T, b: T) -> Bool = compare(a, b) == :gt
  fn ge(a: T, b: T) -> Bool = compare(a, b) != :lt
```

`compare` returns `:lt`, `:eq`, or `:gt`. The helper functions derive boolean
comparisons from it.

## The Functor protocol

```cure
mod Std.Functor
  proto Functor(F)
    fn fmap(container: F, f: A -> B) -> F

  impl Functor for List
    fn fmap(container: List, f: A -> B) -> List =
      Std.List.map(container, f)
```

`fmap` maps a function over a container. Currently only `List` has an
implementation. As new container types are added (Option wrappers, tree
structures), they can implement `Functor` without modifying existing code.

## Cross-module protocol registry (v0.13)

Before v0.13, protocol dispatch was module-local. If `Std.Show` defined
`impl Show for Int`, another module could not call `show(42)` without
importing `Std.Show` and hoping the clauses merged correctly.

v0.13 introduced a global ETS-backed protocol registry. During compilation,
every `impl` block registers itself:

```
ProtocolRegistry.register_impl("Show", "show", "Int", :std_show)
```

Other modules can query the registry:

```
{:ok, :std_show} = ProtocolRegistry.lookup_impl("Show", "show", "Int")
true = ProtocolRegistry.has_impl?("Show", "Int")
```

The registry maps `{protocol_name, method_name, for_type}` to the module
atom that provides the implementation. This enables cross-module dispatch
resolution in the codegen phase.

## Derive mechanism

For record types, you can derive a protocol implementation automatically:

```cure
@derive(Show)
record Point
  x: Int
  y: Int
```

The compiler generates a `show` implementation that prints the record's
fields. The derived output for `Point{x: 3, y: 4}` would be
`"Point{x: 3, y: 4}"`.

Derive works with any protocol that has a sensible default implementation
for record types. Currently `Show` and `Eq` support derivation.

## Building a protocol from scratch: Stringify

Here is a complete example of defining and using a custom protocol:

```cure
mod MyApp.Stringify
  # Define the protocol
  proto Stringify(T)
    fn stringify(x: T) -> String

  # Implement for Int
  impl Stringify for Int
    fn stringify(x: Int) -> String =
      "Int(" <> Std.String.from_int(x) <> ")"

  # Implement for Float
  impl Stringify for Float
    fn stringify(x: Float) -> String =
      "Float(" <> Std.String.from_float(x) <> ")"

  # Implement for String
  impl Stringify for String
    fn stringify(x: String) -> String =
      "String(\"" <> x <> "\")"

  # Implement for Bool
  impl Stringify for Bool
    fn stringify(x: Bool) -> String =
      if x then "Bool(true)" else "Bool(false)"

  # Implement for Atom
  impl Stringify for Atom
    fn stringify(x: Atom) -> String =
      "Atom(:" <> Std.String.from_atom(x) <> ")"

  # Convenience: stringify with newline
  fn stringify_line(x: T) -> String = stringify(x) <> "\n"

  # Use it
  fn main() -> Atom =
    let s = stringify(42) <> " " <> stringify(3.14) <> " " <> stringify(:hello)
    Std.Io.println(s)
```

Calling `main()` prints: `Int(42) Float(3.14) Atom(:hello)`

The generated BEAM code has zero runtime overhead beyond the guard checks
that the BEAM JIT optimizes into jump tables.

## Where constraints (planned)

A planned feature allows constraining type variables in function signatures:

```cure
fn display(x: T) -> String where Show(T) =
  "[" <> show(x) <> "]"
```

The `where Show(T)` clause tells the compiler that `T` must have a `Show`
implementation. At call sites, the compiler verifies the constraint is
satisfied. This is not yet implemented -- currently, protocol calls resolve
dynamically based on the guard dispatch.

## Protocol design guidelines

**One type parameter.** Protocols take a single type parameter. Multi-parameter
type classes are not supported.

**Keep methods minimal.** Define the smallest set of methods in the protocol,
then build helper functions on top. See how `Std.Ord` defines only `compare`
in the protocol and derives `lt`, `le`, `gt`, `ge` as regular functions.

**Bool before Atom.** If your protocol has both `Bool` and `Atom`
implementations, the compiler handles clause ordering automatically. But be
aware that on the BEAM, booleans are atoms.

**Name mangling.** Implementation methods are compiled as private functions
named `method__for__type` (e.g., `show__for__int`). The dispatch function is
the original method name. You cannot call mangled names directly.
