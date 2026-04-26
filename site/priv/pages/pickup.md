%{
  title: "Conditional Dispatch (pickup)",
  description: "The total, ordered, short-circuiting predicate-dispatch construct that replaces if/elif/else. Mandatory else terminator, strict Bool typing, source-order evaluation, refinement narrowing, formatter alignment, and a complete migration story.",
  order: 12
}
---
> **Normative source (v0.33.0).** The `pickup` construct is specified
> at version 1.0.0 in
> [`docs/PICKUP.md`](https://github.com/am-kantox/cure-lang/blob/main/docs/PICKUP.md).
> That document covers the grammar, the static / dynamic / operational
> semantics, the formatter rules, the algebraic laws, the legacy `if`
> migration story, the diagnostic catalogue, and a soundness proof
> sketch. This page is the user-facing tutorial complement; for any
> conflict, the formal specification is the authority.

`pickup` is the only way in Cure to branch on a free-standing boolean
condition. It replaced the legacy `if` / `elif` / `else` chain and is
governed by a single mental model:

> **`pickup` walks the clauses and picks up the first one whose guard
> is true.**

Every other rule in the construct exists to make that intuition
mechanically precise.

## The shape

A `pickup` block is a non-empty list of guarded clauses ending in a
mandatory terminator:

```cure
pickup
  status >= 500 -> :server_error
  status >= 400 -> :client_error
  status >= 300 -> :redirect
  status >= 200 -> :ok
  else          -> :informational
```

Each clause is one of two forms:

- **Guarded** -- `expression -> expression`. The left-hand expression
  is the guard; it MUST type to `Bool`.
- **Terminal** -- `else -> expression`. There is exactly one, and it
  MUST be the last clause. The literal `true` in last position is
  accepted as an alternative form and rewritten to `else` by the
  formatter.

The terminator is mandatory. A `pickup` without `else` (or
last-position `true`) is rejected with `E-PICKUP-NO-ELSE`.

## Total by construction

The mandatory terminator means a well-typed `pickup` cannot fail with
a "no clause matched" condition at runtime. Compare this with `match`:
non-exhaustive `match` is only a warning, and the non-covered case
raises `case_clause` at runtime. With `pickup`, totality is
syntactically guaranteed.

## Strict `Bool` typing

Each guard MUST type to `Bool`. There is no truthy / falsy coercion;
`pickup` is uncompromising about types:

```cure
# Rejected: 1 is not Bool
pickup
  1     -> :truthy
  else  -> :falsy
# E-PICKUP-GUARD-TYPE
```

The branch right-hand sides MUST share a common upper bound under the
language's subtyping relation. If they do not, the program is
rejected with `E-PICKUP-BRANCH-MISMATCH`:

```cure
# Rejected: branches are Int and String
pickup
  cond -> 1
  else -> "two"
# E-PICKUP-BRANCH-MISMATCH
```

## Evaluation order

Guards evaluate in source order. As soon as one yields `true`, no
subsequent guard runs and only the selected branch evaluates. If
every guard yields `false`, the terminator runs.

```cure
pickup
  log "checking ready"  ; ready?    -> launch ()
  log "checking timeout"; timed_out? -> retry ()
  else                                -> wait ()
```

If `ready?` is `true`, `"checking timeout"` is never logged. The
order is contractual, not an optimisation; the compiler rearranges
guards only when their value is statically constant.

## Per-clause scoping

Each clause introduces its own lexical scope:

- A guard `g_i` sees the scope enclosing the `pickup`, extended with
  bindings introduced by `g_i`.
- The right-hand side `e_i` sees the scope of `g_i`.
- Bindings from `g_i`/`e_i` are not visible in any other clause.
- Nothing escapes the `pickup` expression.

## Refinement narrowing

Inside the `i`-th branch, the refinement context is strengthened with
`g_i ∧ ¬g_1 ∧ ... ∧ ¬g_{i-1}`. Inside the `else` branch, it is
strengthened with the conjunction of every preceding negation. This
lets the type checker prove safety of the branch body without an
explicit refinement annotation:

```cure
fn safe_div(n: Int, d: Int) -> Int =
  pickup
    d != 0 -> n / d        # `d` is refined to {x: Int | x != 0}
    else   -> 0
```

## Tail-position behaviour

A branch right-hand side is in tail position with respect to `pickup`
iff `pickup` is itself in tail position. This guarantees proper tail
calls in any branch, including the `else`:

```cure
fn loop(n: Int, acc: Int) -> Int =
  pickup
    n == 0 -> acc
    else   -> loop(n - 1, acc + n)
```

`loop(1_000_000, 0)` terminates without stack overflow.

## `pickup` as an expression

`pickup` is an expression, never a statement. It returns the value
of the selected branch and is admissible everywhere an expression is:

```cure
let label =
  pickup
    n > 0 -> "positive"
    n < 0 -> "negative"
    else  -> "zero"

emit(label)
```

It nests freely with `match` and other constructs:

```cure
match request
  %{method: "GET", path: p} ->
    pickup
      cached?(p) -> serve_cache(p)
      stale?(p)  -> revalidate(p)
      else       -> serve_fresh(p)
  %{method: "POST", body: b} -> handle_post(b)
  _                          -> :malformed
```

## Migrating from `if` / `elif` / `else`

The `if`/`elif` chain has been removed. The `cure rewrite if-to-pickup`
tool migrates surviving code mechanically, preserving comments and
running the formatter on every modified file:

```cure
-- Before (no longer accepted):
if   score >= 90 then "A"
elif score >= 80 then "B"
elif score >= 70 then "C"
else                   "F"

-- After:
pickup
  score >= 90 -> "A"
  score >= 80 -> "B"
  score >= 70 -> "C"
  else        -> "F"
```

Post-migration, the parser rejects `if` with `E-IF-REMOVED` and a
fix-it pointing at the rewriter.

## Formatter conventions

The formatter aligns all `->` tokens within a single `pickup` block,
including the `else` clause:

```cure
pickup
  x > 0     -> :positive
  x < 0     -> :negative
  even?(x)  -> :zero_even
  else      -> :zero_odd
```

Other formatter rules:

- A trailing `true ->` is rewritten to `else ->` with hint
  `H-PICKUP-PREFER-ELSE`.
- A degenerate `pickup` whose only clause is the terminator collapses
  to its right-hand side (`H-PICKUP-DEGENERATE`).
- Multi-line right-hand sides switch every clause in the block to
  the wrapped form (`->` at the end of the guard line, body indented
  one step deeper). Mixing aligned and wrapped forms is forbidden.
- Comments are preserved verbatim. Block-leading and clause-leading
  comments stay attached to their construct under refactoring.
  Internal stray comments may be relocated by the formatter with
  `H-PICKUP-COMMENT-RELOCATED`.
- The formatter is idempotent
  (`format(format(s, c), c) = format(s, c)`) and round-trip-safe
  (formatted source re-parses byte-identically).

## Diagnostics

The full diagnostic catalogue:

- **E-PICKUP-NO-ELSE** -- `pickup` lacks a valid terminator.
- **E-PICKUP-ELSE-NOT-LAST** -- clauses follow the `else` clause.
- **E-PICKUP-MULTIPLE-ELSE** -- more than one `else` clause.
- **E-PICKUP-GUARD-TYPE** -- guard not of type `Bool`.
- **E-PICKUP-BRANCH-MISMATCH** -- branch right-hand sides have no
  common upper bound.
- **E-IF-REMOVED** -- legacy `if` keyword encountered; emitted with
  a fix-it pointing at `cure rewrite if-to-pickup`.
- **W-PICKUP-UNREACHABLE** -- guard provably unreachable.
- **W-PICKUP-DEAD-ELSE** -- terminator provably unreachable.
- **W-PICKUP-EFFECTFUL-GUARD** -- guard observed to have side
  effects.
- **H-PICKUP-PREFER-ELSE** -- trailing `true ->` rewritten to
  `else ->`.
- **H-PICKUP-DEGENERATE** -- single-arm `pickup` collapsed to its
  right-hand side.
- **H-PICKUP-LINE-TOO-LONG** -- clause cannot fit within
  `max_line_width` even when wrapped.
- **H-PICKUP-COMMENT-RELOCATED** -- internal stray comment relocated
  by the formatter.

## Idioms

### Use `pickup` for predicates, `match` for shape

If the deciding question is *"what shape does this value have?"*,
use `match`. If it is *"which of these conditions holds?"*, use
`pickup`. A `match` whose patterns are uniformly wildcards is a
`pickup` in disguise.

### Order guards deliberately

Pick one of two orderings and stay consistent within a block:

1. **By specificity.** More specific predicates first, falling
   through to general ones.
2. **By likelihood.** Most-likely predicates first, optimising the
   cost of evaluation.

### Prefer pure guards

A guard with side effects executes conditionally on every prior
guard's result. Restrict effects to the selected branch unless the
side effect *is* the test (e.g. `lock_acquired?(lock)`).

### Bind once, dispatch many

```cure
# Less clear: each `next_token()` call advances state
pickup
  next_token() == :open  -> parse_block()
  next_token() == :colon -> parse_label()
  else                   -> parse_atom()

# Clearer:
let t = next_token()
pickup
  t == :open  -> parse_block()
  t == :colon -> parse_label()
  else        -> parse_atom()
```

### Use `else`, not `true`

The formatter rewrites `true ->` to `else ->`, but human-written
source SHOULD use `else` directly. The literal `true` reads as if a
real condition is being tested; `else` reads as the default arm.

## See also

- The full normative specification is at
  [`docs/PICKUP.md`](https://github.com/am-kantox/cure-lang/blob/main/docs/PICKUP.md).
- The `match` construct -- the structural-dispatch counterpart -- is
  documented at [`/match`](/match) and specified normatively at
  [`docs/MATCH.md`](https://github.com/am-kantox/cure-lang/blob/main/docs/MATCH.md).
  Both specifications were published into HexDocs in v0.33.0.
- For the broader language reference, see
  [`docs/LANGUAGE_SPEC.md`](https://github.com/am-kantox/cure-lang/blob/main/docs/LANGUAGE_SPEC.md).
