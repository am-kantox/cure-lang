# Proofs in Cure
`proof` containers (v0.19.0) let Cure programs express equality laws
and refinement witnesses as regular source code. Every binding inside
a proof container must elaborate to an `Eq(T, a, b)` type or to a
refinement subtype; the compiler rejects anything else under error
code `E026`.
## Shape
A proof container looks like a module:
```cure
proof Laws.Arithmetic
  fn plus_zero(_n: Int) -> Eq(Int, n, n) = :cure_refl
  fn plus_comm(_a: Int, _b: Int) -> Eq(Int, a, b) = :cure_refl
```
Every function's return type must be `Eq(...)` (or a refinement type
annotation). The body is typically the constant `:cure_refl`, which
is what `Std.Equal.refl/1` returns at runtime. The dependent-type
layer verifies the proposition at compile time; the runtime payload
is erased.
## Why `proof` instead of `mod`
- A container keyword documents intent: everything inside is "laws,
  not computation".
- The type checker only applies the proof-shape gate inside `proof`
  containers, so regular modules remain unrestricted.
- Proof modules live alongside the stdlib: `Std.Proof` ships
  arithmetic and list laws.
## Available laws in `Std.Proof`
| Law | Signature |
|-----|-----------|
| `plus_zero/1` | `Eq(Int, n, n)` |
| `zero_plus/1` | `Eq(Int, n, n)` |
| `plus_comm/2` | `Eq(Int, a, a)` |
| `append_nil/1` | `Eq(List(T), xs, xs)` |
| `map_id/1` | `Eq(List(T), xs, xs)` |
## `assert_type expr : T`
`assert_type expr : T` is a companion feature: a compile-time type
assertion that vanishes at runtime. If the type checker can prove
`expr : T`, codegen strips the wrapper and emits the expression
alone. A mismatch is reported as `E027`.
```cure
fn double(n: Int) -> Int = assert_type n * 2 : Int
```
Use `assert_type` inside regular code when you want the type checker
to confirm a value's type without scattering type annotations on
every `let`.
## Related features
- `Std.Equal` -- `refl`, `sym`, `trans`, `cong` combinators for
  propositional equality.
- `Std.Refine` -- common refinement aliases (`NonZero`, `Positive`,
  `Probability`, ...).
- `Cure.Types.Totality.check_mutual/1` -- mutual-recursion SCC
  analysis (`E029`). Proof containers often involve mutually
  recursive laws; the checker warns when it cannot prove termination
  via structural decrease.
See also `examples/proof_laws.cure` for a runnable example and
`lib/std/proof.cure` for the stdlib laws.
