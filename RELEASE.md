# Cure v0.33.0 -- Formalisation
*The two branching constructs in the language -- `match` and `pickup`
-- graduate from "described in a tutorial" to "specified, normatively,
at version 1.0.0". Two long-form documents land in HexDocs, the
website grows a dedicated `pickup` page, and the language reference
cross-links the new sources of truth.*

Cure is a dependently-typed programming language for the BEAM virtual
machine with first-class finite state machines and SMT-backed
verification.

v0.32.0 was the trust release: proof-carrying packages, cross-language
ADT export, `cure snap`, `cure story`. The compiler caught up with the
ecosystem. v0.33.0 turns the lens inward: with the surrounding
machinery now stable, the time has come to write down precisely what
the two language primitives at the heart of every Cure program *are*.

## What "formalisation" means here

Both specifications follow the same five-stratum layout:

1. **Surface.** Introduction, conformance terminology (RFC 2119
   `MUST` / `MUST NOT` / `SHALL` / `SHOULD` / `MAY`), lexical syntax,
   EBNF grammar.
2. **Semantics.** Static semantics (typing rules, exhaustiveness,
   reachability, scoping, refinement-type interaction, decidability),
   dynamic semantics (evaluation order, side-effect observability,
   exceptions, divergence), and operational semantics (big-step and
   small-step rules, evaluation contexts, determinism, progress,
   preservation, equivalence, confluence, cost and memory models).
3. **Surface conventions.** Formatter rules (alignment, comment
   fidelity, idempotence, round-trip, performance bounds, plugin
   interface, editor-folding integration), interaction with the
   companion construct, worked examples.
4. **Theory and machinery.** Algebraic laws, exception and divergence
   contracts, tail-position behaviour, lowering / compilation rules,
   constant-folding obligations, macro hygiene and quote interaction.
5. **Closure.** Diagnostic catalogue with stable identifiers,
   non-goals, stability and versioning policy, summary.

Eleven appendices follow each: an acceptance test corpus, a glossary,
a per-document change log, an index of normative requirements, a
reference implementation sketch, worked examples, a style guide,
anti-patterns, reserved future syntax, a soundness proof sketch, a
bibliography of related work, open questions for future revisions,
and the colophon.

The implementation already honours every clause of both
specifications. v0.33.0 ships the contract, not a behaviour change.

## `pickup` -- predicate dispatch, made precise

`pickup` is the only way in Cure to branch on a free-standing boolean
condition. It replaced the legacy `if` / `elif` / `else` chain in an
earlier release and ships now with a complete operational story:

```cure
pickup
  status >= 500 -> :server_error
  status >= 400 -> :client_error
  status >= 300 -> :redirect
  status >= 200 -> :ok
  else          -> :informational
```

The mental model is a single sentence that returns repeatedly through
the document: *`pickup` walks the clauses and picks up the first one
whose guard is true.* The specification then makes that intuition
mechanically precise:

- **Total by construction.** The grammar requires the block to
  terminate in `else -> e_else` (canonical) or in a literal-`true`
  guard (alternative form, normalised to `else` by the formatter).
  A well-typed `pickup` cannot fail with a "no clause matched"
  condition at runtime.
- **Strict `Bool` typing.** Every guard MUST type to `Bool`. There is
  no truthy / falsy coercion. A non-`Bool` guard is rejected with
  `E-PICKUP-GUARD-TYPE`.
- **Source-order short-circuit.** Once a guard yields `true`, no
  subsequent guard is evaluated. The order is contractual, not an
  optimisation; reordering by the compiler is admissible only when
  the rearrangement is statically constant.
- **Refinement-context strengthening.** Inside the `i`-th branch the
  refinement context is strengthened with `g_i ∧ ¬g_1 ∧ ... ∧
  ¬g_{i-1}`. Inside `e_else` it is strengthened with the conjunction
  of every preceding negation. v0.30.0's path-sensitive refinement
  flow gets a normative description here.
- **Tail-position guarantee.** A branch right-hand side is in tail
  position with respect to `pickup` iff `pickup` is itself in tail
  position. The classical `loop n acc -> pickup n == 0 -> acc ; else
  -> loop (n-1) (acc+n)` shape is properly tail-recursive.

The formatter chapter is twenty-five clauses long: alignment of
arrows, normalisation of `true ->` to `else ->`, comment fidelity,
idempotence (`format(format(s, c), c) = format(s, c)`), round-trip
(formatted source re-parses byte-identically), performance bounds
(`O(N + M log M)` time, `O(N)` space), and a final formatter grammar.
There is also a migration appendix that walks every legacy
`if`/`elif` shape through the `cure rewrite if-to-pickup` tool and
shows the post-migration source side-by-side.

The full reference is at
[`docs/PICKUP.md`](docs/PICKUP.md).

## `match` -- structural dispatch, made precise

`match` shares the same mental model: *`match` walks the clauses and
picks up the first one whose pattern matches the scrutinee.* It is
the structural counterpart to `pickup`. The specification covers:

- **The full pattern sub-grammar.** Literal patterns, wildcard,
  silent bindings, variable patterns, tuple / list / map / record /
  ADT constructor patterns, repeated variables, the pin operator
  (`^x`), and binary-segment patterns with the full Erlang-style
  specifier chain.
- **Maranget-style exhaustiveness.** The compiler's coverage analysis
  follows the structure of Maranget's *Warnings for Pattern Matching*
  (2007). The specification mandates the algorithm's shape (column
  specialisation, default matrix, recursion on ADT constructors)
  while leaving early termination on the first witness as
  implementation-defined.
- **Refinement narrowing.** Each branch's right-hand side is
  type-checked under a refinement context strengthened by the
  structural assertion that the scrutinee matches the clause's
  pattern, the negation of every preceding pattern, and the user-
  written guard. Pattern-bound variables therefore carry refinement
  information drawn from both structural and predicate constraints.
- **Pattern surface positions.** Patterns are not confined to
  `match`. The same grammar appears in multi-clause function heads,
  `let` bindings, `fn` parameters, comprehension generators, and
  `try ... catch`. The specification cross-references every position
  through the central pattern sub-grammar.
- **Soundness.** Appendix J sketches the standard Progress and
  Preservation argument over the small-step rules SM-Scrut / SM-Hit /
  SM-Skip-Pat / SM-Skip-Guard / SM-NoClause; the corollaries record
  totality (statically exhaustive blocks cannot reach `case_clause`)
  and pattern purity (matching itself contributes no observable
  effects).

Twelve diagnostic codes are catalogued: `E004`, `E021` -- `E025`,
`E031` -- `E034`, plus the warnings `W-MATCH-UNREACHABLE` and
`W-MATCH-COMMENT-RELOCATED`. Every code carries a description, an
example, and fix guidance.

The full reference is at
[`docs/MATCH.md`](docs/MATCH.md).

## Cross-references

`docs/LANGUAGE_SPEC.md`'s `## Pattern Matching` section now opens
with a normative pointer to `docs/MATCH.md`; a new
`## Conditional Dispatch (`pickup`)` section opens with a pointer to
`docs/PICKUP.md` and recapitulates the mental model in one paragraph
for inline readers. Both specifications are wired into the `mix.exs`
docs extras list, so they appear alongside `docs/PATTERNS.md`,
`docs/BINARIES.md`, and the rest of the language references in
HexDocs.

The website gains a new `/pickup` user-facing page, mirroring the
existing `/match` shape, and `/match` itself grows leading and
trailing notes pointing at the new normative documents. The
`/roadmap` page lists v0.33.0 as the most recent implemented release.

## Public surfaces

`docs/MATCH.md` and `docs/PICKUP.md` are the public artefacts. They
are stable at version 1.0.0; future revisions MAY add capabilities
but MUST NOT alter the value, side-effect set, or termination
behaviour of any program conforming to this revision.

## Quiet elsewhere

The compiler surface is unchanged. The stdlib is unchanged. The
package-registry story is unchanged. v0.33.0 is a documentation and
metadata release with one job: take what works, write down what it
is, sign and date it.

## What's next

The long-horizon items carry over. The Cure-native notebook
(`.cnb` format, Livebook-style runner, inline FSM diagrams, live type
hints) moves from v0.33.0's slot to v0.34.0. Typed hot code upgrades
(`cure release --upgrade-from`, SMT-verified `@migration` functions,
E057/E058) keep their cycle. Automatic PGO instrumentation, the
TypeScript and Rust emitters for `cure export-types`, and broader IDE
support (Helix, Zed, an upgraded VS Code extension) remain on the
roadmap.

The repository lives at
[github.com/am-kantox/cure-lang](https://github.com/am-kantox/cure-lang).
The full
[CHANGELOG](CHANGELOG.md)
records every touch point.
