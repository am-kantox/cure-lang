%{
  title: "Pattern Matching",
  description: "Every pattern shape Cure supports: literals, variables, lists, tuples, maps, records, ADTs, bitstrings, pins, repeated variables, guards, nested destructuring, exhaustiveness, and flow-typing.",
  order: 9
}
---
Pattern matching is the primary way Cure programs decompose data and
direct control flow. Every pattern is compiled down to Erlang abstract
forms by `Cure.Compiler.PatternCompiler`, type-checked against the
scrutinee, and analysed for exhaustiveness. Guards, pin equalities, and
repeated-variable equalities are injected as `andalso` guard chains, so
a pattern always succeeds-or-fails atomically.

This page is the authoritative user-facing reference for the language
feature. The on-disk companion document
[docs/PATTERNS.md](https://github.com/am-kantox/cure-lang/blob/main/docs/PATTERNS.md)
describes the AST-to-Erlang lowering in full.

## Where patterns can appear

Patterns are not confined to `match`. The same grammar is accepted in
every one of these positions:

- **`match` expressions**: arm heads and their `when` guards.
- **Multi-clause function heads**: each `| pat -> body` clause.
- **`let` bindings**: `let pat = expr` destructures immediately, with
  a compile-time failure if the pattern is not exhaustive for the
  declared scrutinee type.
- **`fn` parameters**: parameter positions accept the full pattern
  grammar, not just variable names.
- **Comprehension generators**: `for pat <- source` and the
  corresponding filter forms.
- **`try ... catch`**: the `catch` clauses match on the raised value
  the same way a `match` would.

Each clause starts with a fresh scope, so names can be reused freely
between clauses without shadowing warnings.

## Literal patterns

Every literal form that Cure accepts in expression position is also a
pattern. A literal pattern succeeds exactly when the scrutinee is
structurally equal to the literal.

```cure
match n
  0      -> :zero
  1      -> :one
  -1     -> :minus_one        # unary minus is recognised in patterns
  0xFF   -> :byte
  1_000  -> :big
```

Supported literal shapes:

- Integers (`42`, `0xFF`, `0b1010`, `1_000_000`), with unary minus
  accepted as `-42`.
- Floats (`3.14`, `0.001`).
- Strings (`"hello"`), lowered to a `utf8` binary pattern. Byte
  strings lower to a raw binary pattern.
- Atoms (`:ok`, `:error`, `:my_atom`).
- Booleans (`true`, `false`).
- `nil`.
- Characters (`'a'`, `'Z'`).

## Variables, wildcards, and repeated names

A bare identifier binds a fresh variable; the underscore is the
wildcard and binds nothing.

```cure
match value
  _         -> :anything
  x         -> do_something(x)
```

When a name occurs more than once in the same pattern, the compiler
emits a synthetic equality guard: every occurrence must match the same
value.

```cure
match pair
  %[x, x] -> :equal
  _       -> :different
```

The injected guard is conjoined with any user-written `when` clause
via `andalso`, so repeated variables compose cleanly with guards.

## The pin operator `^x`

`^x` compares against an already-bound variable instead of binding a
fresh one. It lowers to a fresh variable plus a synthetic equality
guard against the pre-existing binding.

```cure
let target = get_tag()

match event.tag
  ^target -> :hit
  _       -> :miss
```

If `target` is not in scope at the pin position, the type checker
emits `E024` (unbound pin variable) and the compiler degrades to a
plain binding.

## Lists

Two cons forms are accepted in both pattern and construction position.
Single-head cons matches the head and the tail:

```cure
match xs
  []      -> :empty
  [h | t] -> handle(h, t)
```

Multi-head cons desugars to right-associated cons cells. The pattern
below is identical to `[a | [b | [c | rest]]]`:

```cure
match xs
  [a, b, c | rest] -> a + b + c
  _                -> 0
```

Fixed-size list patterns without a tail also work:

```cure
match xs
  [a, b] -> a + b
  _      -> 0
```

## Tuples

Tuple literals and patterns share the `%[...]` prefix.

```cure
match value
  %[0, 0]     -> :origin
  %[x, y]     -> move(x, y)
  %[_, _, _]  -> :three_elements
```

Tuple patterns recurse into every element, so arbitrary nesting works
out of the box.

## Maps

Map patterns use the `%{...}` prefix. Every key **must be a literal**;
the compiler lowers each field to an Erlang `map_field_exact` entry,
which means the key is required to be present in the scrutinee. Fields
not listed in the pattern are ignored (open matching).

```cure
match request
  %{method: "GET", path: p}   -> fetch(p)
  %{method: m,    path: _}    -> reject(m)
```

A bare identifier at a map-key position is shorthand for `key: key`:

```cure
%{x, y} == %{x: x, y: y}
```

A non-literal, non-identifier map key triggers `E023`.

## Records

Record patterns lower to a map pattern with the implicit
`__struct__ := :tag` guard plus one `map_field_exact` entry per named
field. They participate in schema-driven type checking: referencing a
field that does not exist emits `E021`, and supplying a sub-pattern
whose type does not unify with the declared field type emits `E022`.

```cure
rec Point
  x: Int
  y: Int

rec Person
  name: String
  address: Address

match p
  Point{x: 0, y: 0}                     -> :origin
  Person{name, address: Address{city}}  -> greet(name, city)
```

A bare identifier inside a record pattern is the field-punning
shorthand: `Person{name}` expands to `Person{name: name}`. Unspecified
fields are matched open, so records can be extended without breaking
existing patterns.

## ADT constructors

Constructors of algebraic data types lower to tagged tuples of the
form `{:tuple, L, [tag_atom | child_forms]}`. Any PascalCase name in
function-call position inside a pattern is treated as a constructor
pattern.

```cure
type Option(T) = Some(T) | None
type Result(T, E) = Ok(T) | Error(E)

match opt
  Some(v) -> v
  None()  -> 0
```

Nullary constructors **must** use explicit empty parentheses. A bare
`None` on its own would bind a fresh variable, not match the nullary
constructor.

Constructor patterns recurse into their arguments as patterns, so
nested ADTs decompose in a single arm:

```cure
match x
  Some(Ok(v))   -> v
  Some(Error(_)) -> -1
  None()        -> 0
```

## Nested destructuring

Every shape above composes with every other. The classic stress test
from the v0.18.0 release notes destructures a 3-tuple whose middle
element is a map holding a cons list:

```cure
match value
  %[_, %{list: [head | _]}, _]           -> handle_head(head)
  %[Ok(v), Error(_)]                     -> v
  %[_, %{kind: "event", payload: p}, _]  -> p
  _                                       -> default
```

There is no imposed depth limit.

## Guards

Guards restrict when a clause applies. They appear after `when`, both
in function heads and in `match` arm heads:

```cure
fn classify(x: Int) -> String
  | x when x > 0 -> "positive"
  | x when x < 0 -> "negative"
  | _            -> "zero"

match event
  Msg(s) when Std.String.length(s) > 0 -> s
  Msg(_)                               -> "empty"
  _                                     -> "other"
```

Guards accept the usual set of operators:

- Comparison: `==`, `!=`, `<`, `>`, `<=`, `>=`
- Boolean connectives: `and`, `or`, `not`
- Arithmetic: `+`, `-`, `*`
- Effect-free calls permitted by BEAM guard grammar

Synthetic guards injected by the compiler (pin equalities, repeated
variables) are conjoined with the user-written guard via `andalso`.

## Bitstring patterns

Since v0.20.0, bitstring patterns accept the full Elixir-style segment
grammar. Segments inside `<<...>>` carry type, size, endianness,
signedness, and unit specifiers chained with `-`:

```cure
match packet
  <<tag::utf8, size::16, payload::binary-size(size), rest::binary>> ->
    decode(tag, payload, rest)
  _ -> :malformed
```

The specifier grammar mirrors Erlang's exactly. Type atoms are
`integer`, `float`, `bits`, `bitstring`, `bytes`, `binary`, `utf8`,
`utf16`, `utf32`. Endianness (`big` / `little` / `native`),
signedness (`signed` / `unsigned`), and size/unit (`size(n)`,
`unit(u)`) are optional and carry Erlang's defaults:
`integer-unsigned-big-size(8)-unit(1)`. A bare integer after `::` is
shorthand for `size(n)`.

```cure
match bin
  <<x::8>>            -> x           # same as <<x::size(8)>>
  <<x::32-signed>>    -> x           # signed big-endian integer
  <<x::float-little>> -> x           # 64-bit little-endian float
```

## Negated literals

Unary minus in a pattern position compiles to the negated literal, so
`-5` matches the integer `-5`. This works for both integer and float
literals.

```cure
match temperature
  -273 -> :absolute_zero
  0    -> :freezing
  n    -> n
```

## Exhaustiveness

The type checker runs two passes after every pattern-bearing
construct:

1. A **flat** classifier that recognises `:wildcard`, `:empty_list`,
   `:cons`, `{:literal, subtype, value}`, `{:constructor, name, n}`,
   `{:tuple, n}`, `{:map, n}`, and `{:record, name, fields}` at the
   top level of each arm. Missing shapes are reported as `E004`.
2. A **Maranget-style** nested pass that descends into tuple
   scrutinees whose element types are enumerable (`Bool`,
   `Result(T, E)`, `Option(T)`). Missing witnesses are rendered as
   source-shape strings and reported as `E025`.

```text
Warning: match expression has nested non-exhaustive cases (E025)
  missing: %[Error(_), _]
```

Both passes emit `:type_warning` events via the pipeline. They do not
block compilation: you can still build the program, but the warnings
remain until the gap is closed.

For infinite types (`Int`, `Float`, `String`), a trailing wildcard `_`
is required for exhaustiveness; you cannot enumerate all integers.

## Error codes

The pattern engine contributes the following dedicated error codes,
each available via `cure explain Edd` or `cure why Edd`:

- **E004** - non-exhaustive patterns (flat classifier).
- **E021** - unknown record field in a record pattern.
- **E022** - record-pattern field type mismatch.
- **E023** - non-literal, non-identifier map-pattern key.
- **E024** - unbound pin variable.
- **E025** - non-exhaustive nested match (Maranget walker).

## Path-sensitive refinement

Pattern matches narrow the type of their scrutinee along each arm.
`Cure.Types.PathRefinement` threads the arm's implied constraints
back into the type environment so that subsequent expressions see a
more precise type.

```cure
if x != 0 then 100 / x else 0
```

Inside the `then` branch `x` is refined to `{x: Int | x != 0}`, so the
division is safe without an explicit refinement annotation.

## Structural refinement narrowing

v0.20.0 ships `Cure.Types.PatternRefinement`, whose `narrow/2` takes a
pattern AST and a scrutinee type and returns
`{bindings, narrowed_scrutinee}`. Two kinds of witnesses come back:

**Literal-equality witnesses.** A sub-pattern that is a literal means
the matched value *is* that literal along the arm. Matching `0`
against `Int` narrows the scrutinee to `{x: Int | x == 0}`; inside a
tuple pattern the other slots keep their original element types.

**Disjoint-tag witnesses.** A constructor pattern (`Ok(v)`,
`Error(e)`) or a map pattern with a literal `:kind` tag narrows the
scrutinee to a tagged variant:

```elixir
narrow({:function_call, [name: "Ok"], [{:variable, [], "v"}]}, :any)
# => {%{"v" => :any}, {:variant, :ok, []}}
```

Every narrowed type is something the SMT translator already
understands, so `PatternRefinement` integrates directly with the
existing refinement machinery.

## Worked example: JSON-shaped data

The example below uses only pattern matching -- no recursion helper,
no conditional expression -- to classify a JSON-shaped value across
five constructor variants, each with a different secondary shape:

```cure
type Json =
  | JNull
  | JBool(Bool)
  | JInt(Int)
  | JStr(String)
  | JArr(List(Json))
  | JObj(List(Tuple))

fn is_truthy(j: Json) -> Bool =
  match j
    JNull()    -> false
    JBool(b)   -> b
    JInt(0)    -> false
    JInt(_)    -> true
    JStr("")   -> false
    JStr(_)    -> true
    JArr([])   -> false
    JArr(_)    -> true
    JObj([])   -> false
    JObj(_)    -> true
```

Every arm combines constructor destructuring with a literal-equality
witness (`0`, `""`, `[]`) to decide truthiness without a single
conditional.

## Limitations

A small set of pattern shapes are reserved for future versions:

- **Range patterns** (`1..10 -> ...`) are compile-time rejected.
- **Bitstring segment specifiers** beyond integer and variable tails
  were only partial before v0.19.0; the current parser accepts the
  full grammar, but a handful of Erlang-level segment combinations
  still fall through to the interpreter rather than the native
  compiler. They are accepted by the surface syntax and documented as
  experimental.
- **Regex patterns** are not part of the surface language; use
  `Std.Regex` in expression position instead.

See `examples/destructuring.cure`, `examples/json_tree.cure`, and
`examples/pattern_guards.cure` for end-to-end programs that exercise
every shape on this page.
