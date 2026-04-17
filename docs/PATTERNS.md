# Cure Pattern Matching Reference
This document is the authoritative reference for Cure's pattern
matching. It covers every pattern shape accepted by `match`, `let`,
multi-clause function heads, comprehension generators, and `try ...
catch` clauses.

## Pattern AST to Erlang mapping

The pattern compiler lives in `Cure.Compiler.PatternCompiler`. It
lowers MetaAST pattern nodes into Erlang abstract forms. The table
below is the contract you can rely on when inspecting compiler output
or writing Elixir-side tooling.

- `{:variable, _, "_"}` lowers to `{:var, L, :_}` (wildcard).
- `{:variable, _, name}` on first occurrence lowers to
  `{:var, L, :V_name}` and adds `name` to the scope. On a repeat it
  lowers to a fresh variable and emits an equality guard against the
  original binding.
- `{:pin, _, [{:variable, _, name}]}` lowers to a fresh variable plus
  an equality guard against the pre-existing binding for `name`. If
  `name` is unbound at that point, the type checker emits `E024` and
  the compiler falls back to a plain binding.
- `{:literal, [subtype: :integer], n}` lowers to `{:integer, L, n}`.
  Similarly for `:float`, `:symbol`, `:boolean`, `:null`, `:char`.
  Strings lower to a utf8 binary pattern; byte strings to a raw
  binary.
- `{:tuple, _, elems}` recurses into every child as a pattern and
  lowers to `{:tuple, L, forms}`.
- `{:list, [cons: true], [head, tail]}` lowers to
  `{:cons, L, head_form, tail_form}`.
- `{:list, _, elems}` (without `cons`) lowers to the Erlang cons
  chain `{:cons, L, e1, {:cons, L, e2, ... {nil, L}}}`.
- `{:map, _, pairs}` lowers to a map pattern. **Each field uses
  `map_field_exact`**, so the pattern requires the key to be present
  in the subject.
- `{:function_call, [record: true, name: T], fields}` lowers to a
  map pattern with `__struct__ := :t` plus one `map_field_exact`
  entry per field. Field-punning shorthand (bare `{:variable, _,
  name}` inside `fields`) expands to `name: name`. Unspecified fields
  are ignored (open matching).
- `{:function_call, [name: Tag], args}` with a PascalCase `Tag` is an
  ADT constructor pattern. It lowers to a tagged tuple
  `{:tuple, L, [{:atom, L, tag} | child_forms]}`, recursing into each
  argument as a pattern.
- `{:unary_op, [operator: :-], [literal]}` in a pattern compiles to
  the negated literal (so `-5` matches the integer `-5`).

## Binding and scope

Pattern variables are introduced into the enclosing scope and become
available to:

- The arm's `when` guard (and to any injected pin/repeat guards).
- The arm's body.
- The rest of the block (for `let` destructuring).

In multi-clause functions each clause starts from a fresh empty
scope, so names can be reused freely across clauses.

## Map keys in pattern position

Map keys in a pattern must be literal values (atoms, integers,
strings, ...). A bare identifier at a map-key position is permitted
as an abbreviation: `%{x, y}` expands to `%{x: x, y: y}`. Any
non-literal non-identifier expression triggers `E023`.

## Record fields

Record patterns resolve against the record's declared schema when the
type is known. Referring to a field that is not in the schema emits a
`E021` warning. Providing a sub-pattern whose type is incompatible
with the declared field type emits `E022`.

## Exhaustiveness

The type checker runs two passes:

1. A **flat** classifier that recognises `:wildcard`, `:empty_list`,
   `:cons`, `{:literal, subtype, value}`, `{:constructor, name, n}`,
   `{:tuple, n}`, `{:map, n}`, and `{:record, name, fields}` at the
   top level of each arm. Missing shapes are reported as `E004`.
2. A **nested** pass (Maranget-style, best-effort) that descends into
   tuple scrutinees whose element types are enumerable (Bool,
   Result, Option). Missing witnesses are rendered as source-shape
   strings and reported as `E025`.

Both passes emit `:type_warning` events via the pipeline. They do
not block compilation.

## Injected guards

`Cure.Compiler.PatternCompiler` can add synthetic guards to a clause
when the pattern uses:

- `^x` (pin operator).
- A variable that occurs more than once in the same pattern.

These are conjoined with the user-written `when` clause via
`andalso` before being emitted into the Erlang abstract form.

## What is not supported (yet)

- Multi-head cons patterns such as `[a, b | rest]`. Use nested
  `match` or the helpers in `Std.Match`.
- Range patterns (`1..10 -> ...`). Compile-time rejected.
- Bitstring patterns with complex segment specifiers (`x:8/integer,
  rest/binary`). The parser accepts `<<...>>` literals; the
  pattern compiler only handles integer segments and bare variable
  tails today. Full segment specifiers land in v0.19.0.

See `docs/LANGUAGE_SPEC.md` §"Pattern Matching" for the surface
syntax, `examples/destructuring.cure`, `examples/json_tree.cure`,
and `examples/pattern_guards.cure` for end-to-end programs, and
`Std.Match` for stdlib helpers.
