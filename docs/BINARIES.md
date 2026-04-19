# Binaries

Reference guide for Cure's binary literal and pattern syntax.
Introduced in v0.20.0 (segment AST, codegen, printer) and completed
in v0.21.0 (type-checker bindings, exhaustiveness via `E031`).

## Syntax

A binary literal is written between `<<` and `>>`, with segments
separated by commas. Every segment has the shape:

```
value [:: specifier_chain]
```

The specifier chain is a hyphen-joined list of specifiers (mirroring
Elixir's grammar):

- **Type**: `integer`, `float`, `bits`, `bitstring`, `bytes`, `binary`,
  `utf8`, `utf16`, `utf32`.
- **Signedness**: `signed`, `unsigned`.
- **Endianness**: `big`, `little`, `native`.
- **Size**: `size(expr)`. A bare integer specifier is shorthand for
  `size(<integer>)`.
- **Unit**: `unit(n)`.

Defaults mirror Erlang: `integer-unsigned-big-size(8)-unit(1)`; the
`utf8`, `utf16`, and `utf32` types carry their own implicit size.

## Examples

```cure
## Construct a 4-byte record.
let header = <<42, 1, 2, 3>>

## Destructure the first byte; rest::binary captures the remaining
## bytes as a Bitstring.
match buf
  <<b, _rest::binary>> -> b
  <<>>                 -> 0

## Fixed-width: read a 16-bit big-endian integer.
let <<len::16, payload::binary-size(len), _::binary>> = frame
```

## Pattern positions

Binary patterns work in every destructuring position:

1. `match` arms.
2. Multi-clause function heads: `fn parse(buf: Bitstring) -> Int | <<a, _rest::binary>> -> a | <<>> -> 0`.
3. `let` bindings: `let <<tag, body::binary>> = buf`.

Comprehension generators with a binary source (`for <<b <- buf>>`)
are reserved for a future release.

## Type-checker semantics

`Cure.Types.Checker.bind_pattern_vars/3` gained a `:bin_segment`
clause in v0.21.0. Every segment's inner variable picks up the
type implied by the segment specifier:

| Specifier type        | Bound variable type |
| --------------------- | ------------------- |
| `integer` (default)   | `Int`               |
| `float`               | `Float`             |
| `utf8` / `utf16` / `utf32` | `Char` (code point) |
| `binary` / `bytes` / `bitstring` / `bits` | `Bitstring` |

Where the checker can prove a byte-size refinement on the
scrutinee, it propagates the narrowing through the segments. The
v0.21.0 propagation is conservative: a trailing `rest::binary` binds
to plain `Bitstring`. Future releases will emit
`byte_size(rest) == byte_size(scrutinee) - sum_of_preceding_sizes`
once the SMT translator gains the corresponding arithmetic.

## Exhaustiveness

`Cure.Types.PatternChecker.check_binary_exhaustiveness/2` runs
whenever the scrutinee of a `match` is a `Bitstring` (or a
`Bitstring` refinement). It reports `E031` when a set of arms does
not cover every inhabitant:

- A top-level wildcard (variable binding) covers everything.
- A binary pattern whose last segment is an open-ended tail
  (`::binary`, `::bits`, `::bitstring`, `::bytes` with no `:size`)
  covers every non-empty suffix.
- The empty binary `<<>>` covers the zero-byte case.

A set of arms is exhaustive if at least one arm is a wildcard, or
if both the empty and open-tail cases are covered. Otherwise the
compiler prints a concrete witness such as `"<<>>"` or
`"<<_, _rest::binary>>"`.

## Codegen

Binary patterns lower directly to Erlang's `:bin_element` form.
Construction uses the same AST shape as patterns, so
`<<x::utf8, rest::binary>>` emits a matching binary with the
correct size/type/unit/sign/endian tuples.

See also: `docs/PATTERNS.md` for the broader destructuring
reference and `docs/LANGUAGE_SPEC.md` for the full grammar.
