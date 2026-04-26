# Cure TODO Ideas

A running brainstorm of features, tools, and weird-but-beautiful
experiments that Cure could ship in future releases. Items tagged
`[v0.27.0]` are accepted into the current release plan; the rest are
parked here for later triage.

Items accepted into v0.27.0 are, as a group, themed
**"See Your System Breathe"** -- the natural follow-up to v0.26.0's
"Applications and Releases".

## Big themes that fit the trajectory

### 1. `cure top` -- observability TUI  [v0.27.0]
An htop-style TUI over a running Cure release: supervisors on top,
actors below, per-actor mailbox depth, last message type, GC,
reductions, effect counters. Uses `marcli` so it inherits the theme
from the REPL.

### 2. `cure trace <Module.fun/arity>` -- typed tracer  [v0.27.0]
Typed `:dbg` replacement that shows arguments with their *types*,
not raw Erlang terms. Filter by effect (`--effect Io`), by refinement
violation, by message shape.

### 3. Time-travel for FSMs and actors
Every `on_transition` and `on_message` can opt into `@record` which
journals `(state_before, event, state_after, timestamp)` to disk;
`cure replay <trace>` re-plays it against a fresh process,
single-stepping in the REPL.

### 4. Auto-generated Mermaid diagrams  [v0.27.0]
Have `cure doc` emit a Mermaid diagram per FSM (states + edges with
`!`/`?` annotations) and per supervisor tree (with child policies).
Ship a `--svg` flag via `mermaid-cli`.

### 5. OpenTelemetry bridge (`Cure.OTel`)  [v0.27.0]
Auto-instrument actor sends (the Melquiades Operator is a natural
trace-propagation point), FSM transitions, and SMT queries,
exporting via OTLP. Layered on the existing `Cure.Telemetry`.

### 6. Algebraic effect handlers
`handle expr with { Io.println(s) k -> ... | Exception(e) k -> ... }`
for one-shot handlers a la OCaml 5 / Eff. First-class user-defined
effects via `effect` declarations, capability-scoped effects
(`! Io<stdout>` vs `! Io<stderr>`), typed continuations.

### 7. Session types for actors (`protocol` container)  [v0.27.0]
Declares a binary protocol between two parties as a finite state
machine over message types. The compiler verifies that each
participant actor respects the protocol via structural checks plus
SMT for branching/looping. Add `E056 Protocol Violation`.

### 8. New stdlib: `Std.CRDT`, `Std.Time`, `Std.Regex`  [v0.27.0]
- `Std.CRDT` -- `GCounter`, `PNCounter`, `ORSet`, `LWWRegister`,
  `MVRegister`. Thin layer over `:erlang` terms with refinement
  types guaranteeing commutativity and idempotence through proof
  obligations; integrates with `Std.Proof`.
- `Std.Time` -- ISO8601 parsing, `Duration`, `Instant`, timezone
  helpers layered on OTP's `Calendar`/`DateTime`.
- `Std.Regex` -- regex wrapper with compile-time validation plus
  refinement-typed `Matched(n)` results so callers can destructure
  capture groups safely.

### 9. Typed hot code upgrades
`cure release --upgrade-from 0.1.0` diffs the new release against
the previous `.rel` and generates a typed `.appup`. SMT-verified
state migration functions. New error codes `E057 Unmigrated State`,
`E058 Migration Violates Invariant`.

## Developer UX -- polish that users feel

### 10. Cure-native notebook
A first-class `.cnb` format (or `.cure.livemd`) evaluated by a
Livebook-style runner. Syntax-highlighted via `makeup_cure`,
diagrams inline from FSMs, live type hints.

### 11. Typed holes with synthesis  [v0.27.0]
Extend `?` holes (v0.17.0) with `cure synth path/file.cure:line`
that searches the local env + stdlib for well-typed completions and
offers the top-3 with effect annotations. REPL `:synth`.

### 12. REPL `:play` and `:sketch`
`:play` -- throwaway buffer with live preview that re-typechecks
and shows inferred types inline on every keystroke. `:sketch` --
whiteboard mode for drawing FSM graphs with arrow keys, exportable
to Cure source.

### 13. Parser error recovery
Add recovery points at `end`/indent-dedent boundaries so a single
file emits *all* errors in one pass instead of stopping at the
first.

### 14. `cure fmt --diff`
Use `marcli` to render red/green diffs inline. Paired with the
algebra formatter (v0.20.0).

### 15. `cure story`
Reads a project and generates a narrative `STORY.md` introducing
the system top-down: apps -> supervisors -> actors -> FSMs -> types.

### 16. "Did you mean?" everywhere
Extend Levenshtein suggestions (v0.12.0) to record fields, FSM
events, protocol methods, `Cure.toml` keys, CLI subcommands,
`Std.*` imports.

## Strictly weird and beautiful

### 17. `temporal` container  [v0.27.0]
Attach live-ness and safety claims to an FSM:
`temporal Turnstile { always eventually Unlocked; never Dead }`.
Feed the FSM's transition graph to a bounded model checker (or
reuse Z3). Failed properties raise `E059 Temporal Property Violated`
with a minimal counterexample trace.

### 18. Cure Shell (`cure sh`)
A POSIX-ish shell whose commands are Cure expressions.
`ls | filter(&.is_file?) |> map(&.size) |> sum` is real Cure via a
new `Std.Os`.

### 19. ASCII-art diagrams in the terminal
`cure draw fsm Turnstile`, `cure draw sup Colony`, `cure draw app Forge`
emit braille/ASCII art of the structure. Optionally
`--kitty-graphics` for Kitty-protocol images.

### 20. Music from FSMs (`cure sing`)
Map states to MIDI notes, transitions to note changes, replay an
execution trace as a melody. Adjacent: `examples/cure_motif/` ships a
length-indexed step sequencer with an `@record`-annotated envelope
FSM, a three-actor supervision tree, `Cure.Temporal` liveness proofs,
and an ASCII piano-roll renderer -- the "FSM as music" half of the
idea already exists in runnable form.

### 21. WASM playground  [v0.27.0]
Compile `Cure.Types.Checker` + parser to WASM and publish as
`cure-lang.org/playground`. Docs pages get live executable snippets.

### 22. Hyperlink-aware errors  [v0.27.0]
File paths in error messages become OSC 8 hyperlinks in supported
terminals (WezTerm, Kitty, iTerm, VTE, Warp). Matches the
marcli-rendered REPL aesthetic.

### 23. Collaborative REPL over distribution
`cure repl --attach <node@host>` joins an existing REPL session;
all participants see each other's input and output. The session is
itself an actor.

### 24. `cure bless` -- Socratic assistant
Reads a failing typecheck and walks the user through fixing it
interactively ("the checker expected `Nat`, you gave `Int`; refine
with `require n >= 0` -- do it? [y/n]"). Pairs with typed holes
and synthesis.

### 25. Additional ideas parked
The following ideas remain in the brainstorm pool without explicit
numbering; each is worth its own detailed spec before promotion:
- `Std.Describe` -- self-describing types with derivable prose.
- `cure release --oci` -- OCI image output with BEAM and release
  baked in.
- Cross-language ADT export (TypeScript, Rust) -- v0.32.0 shipped
  Protobuf; TypeScript and Rust targets are future work.

## v0.27.0 -- accepted bundle

Theme: **"See Your System Breathe"**. The following items are
accepted into v0.27.0:

- Item 1: `cure top` observability TUI
- Item 2: `cure trace` typed tracer
- Item 4: Auto-generated Mermaid diagrams in `cure doc`
- Item 5: OpenTelemetry bridge (`Cure.OTel`)
- Item 7: Session types between actors (`protocol` container)
- Item 8: New stdlib: `Std.CRDT`, `Std.Time`, `Std.Regex`
- Item 11: Typed holes with synthesis
- Item 17: `temporal` container + bounded model checking
- Item 21: WASM playground on cure-lang.org
- Item 22: Hyperlink-aware errors
- Showcase example: `examples/cure_atelier/` -- an observability-
  focused app that uses OTel plus a temporal property plus a
  session-typed protocol end-to-end, the way `cure_forge` showcased
  v0.26.0.

## Notes on scope counting

The original brainstorm grouped the shipped work into nine bundles;
flattened into individual TODO items that expands to ten (items 1,
2, 4, 5, 7, 8, 11, 17, 21, 22) plus the `cure_atelier` showcase.
Items 1 and 2 together form the observability duo in the original
count of nine.

## v0.32.0 -- accepted bundle

Theme: **"Trust, Export, Recall, Narrate"**. The following items are
accepted into v0.32.0:

- Proof-carrying packages -- `.cureproof` artifacts embedded in
  published tarballs; `cure verify` for offline re-verification.
  New error codes E065, E066, E067.
- Cross-language ADT export -- `cure export-types --target protobuf`
  targeting proto3. New error code E068.
- `cure snap` -- save/load the entire REPL environment into
  `.cure-snap` files. New error codes E069, E070. REPL meta-commands
  `:snap save`, `:snap load`, `:snap list`.
- `cure story` -- reads a project and generates a narrative `STORY.md`
  introducing the system top-down: apps -> supervisors -> actors ->
  FSMs -> types. Supports `--diagrams` (Mermaid) and `--format html`.

## v0.33.0 -- accepted bundle

Theme: **"Formalisation"**. The two branching constructs in the
language -- `match` and `pickup` -- graduate from "described in a
tutorial" to "specified, normatively, at version 1.0.0". v0.33.0
ships the contract, not a behaviour change: the implementation
already honours every clause of both specifications.

- **`docs/MATCH.md`** -- *The `match` Construct, Language
  Specification, Version 1.0.0*. EBNF grammar, the full pattern
  sub-grammar, T-Match typing, Maranget-style exhaustiveness,
  refinement narrowing, big-step / small-step operational semantics,
  twenty-five formatter-conformance clauses, the diagnostic catalogue
  (`E004`, `E021`-`E025`, `E031`-`E034`), the soundness proof sketch,
  and reserved future syntax (or-patterns, view patterns, range
  patterns, dependent patterns, as-patterns).
- **`docs/PICKUP.md`** -- *The `pickup` Construct, Language
  Specification, Version 1.0.0*. T-Pickup-Else / T-Pickup-Cons,
  totality enforced by the mandatory terminator, source-order
  short-circuit semantics, refinement-context strengthening, the
  migration story for legacy `if` / `elif`
  (`cure rewrite if-to-pickup`, `E-IF-REMOVED`), the diagnostic
  catalogue (`E-PICKUP-NO-ELSE`, `E-PICKUP-ELSE-NOT-LAST`,
  `E-PICKUP-MULTIPLE-ELSE`, `E-PICKUP-GUARD-TYPE`,
  `E-PICKUP-BRANCH-MISMATCH`), reserved future syntax (`pickup as`,
  `pickup with`, `pickup async`, trailing `where`).
- **HexDocs integration** via `mix.exs` `docs.extras`.
- **`docs/LANGUAGE_SPEC.md`** cross-references both as the normative
  sources of truth.
- **Website** -- new `/pickup` page mirroring the existing `/match`
  shape; `/match` itself grew leading and trailing notes pointing at
  the new normative documents; `/roadmap` and `/tooling` updated
  accordingly.
- **Blog post** -- `site/priv/posts/2026/04-26-cure-v0.33.0.md`.
- **No language-surface behaviour changes.** Code that compiled and
  ran under v0.32.0 compiles and runs identically under v0.33.0.

## v0.34.0 -- planned next sprint

Theme: **"Cure-native notebook"** (Item 10 from the brainstorm pool).

A first-class `.cnb` format (or `.cure.livemd`) evaluated by a
Livebook-style runner. Syntax-highlighted via `makeup_cure`, diagrams
inline from FSMs, live type hints. Foundation already in place:
`makeup_cure` for highlighting, `Cure.Doc.Mermaid` for diagrams,
`Cure.REPL` evaluation pipeline for live code cells.
