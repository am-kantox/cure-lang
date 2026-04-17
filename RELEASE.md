# Cure v0.18.0 -- Deep Destructuring
*Pattern matching grows up.*

Cure is a dependently-typed programming language for the BEAM virtual
machine with first-class finite state machines and SMT-backed
verification.

v0.18.0 rebuilds Cure's pattern matching into a deeply-recursive
engine. `match` and `let` now destructure arbitrary nesting across
tuples, lists (both fixed and cons), maps, records, and ADT
constructors -- in any combination, at any depth. The previously
flat pattern code was quietly miscompiling map patterns and never
descending into nested shapes; v0.18.0 replaces it wholesale.

## Headline feature

```cure
match value
  %[_, %{list: [head | tail]}, _] -> handle(head, tail)
  Person{name, address: Address{city}} when city == "Madrid" ->
    greet(name)
  [Ok(v) | _] -> v
  _ -> default
```

Everything in that snippet now works. Each sub-pattern is compiled as
a real pattern, not as an expression that accidentally happens to be
valid in that position.

## What's new

### `Cure.Compiler.PatternCompiler`

A dedicated pattern-to-Erlang translator, separated from the
expression code generator. Every pattern node is dispatched through
a single recursive entry point and lowers to the correct Erlang
abstract form:

- Tuple patterns, fixed list patterns, and cons patterns recurse
  into their children.
- Map patterns emit `map_field_exact` (`:=`), not `map_field_assoc`
  (`=>`). Until now map patterns silently matched everything.
- Record patterns lower to map patterns with `__struct__ := :tag`
  plus exact entries per field; unspecified fields are open-matched.
- ADT constructor patterns lower to tagged tuples whose children are
  themselves patterns.
- Field punning: `Point{x, y}` is shorthand for `Point{x: x, y: y}`.
- Pin operator `^x` compares against a previously-bound value, not a
  fresh binding. Lowered to a synthetic equality guard.
- Repeated variables inside the same pattern are lowered to equality
  guards too; `%[x, x]` now matches exactly the pairs where the two
  slots are equal.

### Type-checker rewrite

`Cure.Types.Checker.bind_pattern_vars/3` is rebuilt with deep
recursion: every leaf pattern variable picks up the most precise type
that the structure allows. Map and record patterns narrow per-field
through the record schema; tuple patterns zip against the scrutinee
tuple-element types.

A new Maranget-style nested-exhaustiveness pass in
`Cure.Types.PatternChecker.check_nested/2` walks tuple-of-ADT
scrutinees and reports concrete missing witnesses (for example
``"%[Error(_)]"``) as warnings under code `E025`. The flat classifier
from v0.11.0 remains as the fast path for simple matches.

### New error codes

`E021`-`E025` in the catalog: unknown record field in pattern,
record-field type mismatch, non-literal map-pattern key, unbound pin
variable, non-exhaustive nested match. Surfaced via `cure explain Exxx`.

### Parser

- Lexer already emits `:caret`; the parser now turns it into the
  `{:pin, meta, [inner]}` prefix node.
- Field-punning in record and map pairs: a bare identifier followed
  by `,` or `}` desugars to `name: name`.

### Standard library

- New `Std.Match` module -- destructuring helpers (`unpack_pair/1`,
  `fst/1`, `snd/1`, `head_tail/2`, `uncons/1`, `first_two/2`,
  `unwrap_ok/2`, `unwrap_some/2`). Every function exercises the new
  pattern engine as a smoke test.
- `Std.List.uncons/1`, `Std.List.split_first/2` added using cons
  destructuring.

### Examples

- `examples/destructuring.cure` -- end-to-end showcase of nested
  tuples, maps, records, cons, ADT constructors, and the pin operator.
- `examples/json_tree.cure` -- small JSON-like interpreter driven
  entirely by nested destructuring.
- `examples/pattern_guards.cure` extended with record patterns,
  field-punning, and nested ADT destructuring.

### Documentation

- `docs/PATTERNS.md` -- the authoritative reference (Cure surface
  syntax, Erlang abstract-form mapping, binding semantics,
  exhaustiveness behaviour).
- `docs/LANGUAGE_SPEC.md` pattern-matching section rewritten from a
  12-line stub.
- `docs/TUTORIAL.md` -- new chapter "Destructuring in `match`"; later
  chapters renumbered.

## Deferred to v0.19.0

The original v0.18.0 "Bring the Furniture" slate is now the v0.19.0
roadmap: `proof` containers, `assert_type`, record field defaults,
`@derive(Show, Eq, Ord)` wiring, property-based testing via
`Std.Test.forall`, `Std.Iter`, the first half of the package
registry, and mutual-recursion totality. The pin operator also
graduates to default in v0.19.0 after v0.18.0 feedback.

## Numbers

- 1 new Elixir module (`Cure.Compiler.PatternCompiler`, ~480 LOC)
- Rewrites inside 3 existing modules (`Codegen`, `Checker`,
  `PatternChecker`)
- 1 new stdlib module (`Std.Match`), 1 extended (`Std.List`)
- 2 new examples, 1 extended
- 2 new documentation files (`PATTERNS.md`, new tutorial chapter)
- New error codes `E021`-`E025`
- 26 new tests (22 for `PatternCompiler`, 2 for parser, others
  driven by new examples); total jumps to 921 tests passing
- All 21 stdlib modules and 26 example programs compile clean under
  `mix check`.

## Naming

"Deep Destructuring" -- subtitled *Pattern matching grows up*.
