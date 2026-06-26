# Autopilot completion report — Std.Signal v2 combinators

**Branch:** `autopilot/std-signal` (NOT merged — operator merges on return)
**Date:** 2026-06-27
**Result:** ✅ Success. All stages complete; full stdlib suite green (337 passed, 0 failures).

## What this run delivered

Two things the operator asked for in one autonomous run:

1. **Research finding (variadic merge):** Can Cure's dependent types express a
   true variadic `merge(a, b, c, …)` whose arity is a parameter, specialised to
   fixed-arity BEAM functions? **Answer: no, not today** — backed by two
   compiler facts (no large elimination / `Nat -> Type` recursion; monomorph
   is type-keyed and arity-preserving). Documented in the spec §3. Decision:
   ship the list form `merge_all(List(Signal(A)))`.

2. **v2 combinator set (13 functions)** appended to `lib/std/signal.cure`,
   each TDD-verified. Std.Signal now totals **30 combinators** (17 v1 + 13 v2),
   100% pure Cure, FFI-free, AtomVM-friendly.

### The 13 v2 combinators

| Group | Functions |
|---|---|
| Stateless | `merge_all`, `filter_map`, `unzip`, `partition`, `sample`, `meta`, `unmeta` |
| Stateful (state-in/state-out) | `map2` (combine_latest), `zip`, `throttle` (leading-edge), `toggle`, `running_sum`, `running_mean` |

Plus two private helpers (`sig_or`, `either_present`) backing `map2`/`zip`.

## Per-stage outcomes & commits

| Stage | Outcome | Commit(s) |
|---|---|---|
| 0 — Research + spec | Variadic-merge finding + 13-combinator design written | `82d123b` |
| 1 — Spec review (subagent, recursive-skeptical) | Hardened to 2 clean passes | `7620406` |
| 2 — Plan | 6 TDD task-groups, exact Cure + ExUnit code | `80d1cfc` |
| 3 — Plan review (subagent, recursive-skeptical) | Converged in 5 passes; 2 findings fixed (zip/running_sum absent+handoff coverage; v2-test immutability rule) | `3db9026` |
| 4 — Execute (inline TDD, red→green→commit per group) | 6 task-groups, 19 new tests, all green | `acfdad0` `01fb642` `3ad86ec` `0c931c3` `cc9b5eb` `00f7553` |
| 5 — Verify + report + notify | Full `test/cure/stdlib/` suite: **337 passed, 0 failures** | (this report) |

## Verification

- `mix test test/cure/stdlib/cure_std_signal_test.exs`: **54 passed** (35 v1 + 19 v2).
- `mix test test/cure/stdlib/` (whole suite, regression gate): **337 passed, 0 failures.**
- TDD discipline held: every task-group ran red (undefined-function failures
  for exactly the new names) before green; assertions stayed immutable.

## Notes for the operator

- **No auto-merge.** Review and merge `autopilot/std-signal` when ready.
- No new example program was added — v1's `signal_sensor.cure` already proves
  runnable multi-module integration; v2's surface is unit-verified (per spec §6).
- **Out of scope / deferred** (spec §7, unchanged): true variadic dependent
  `merge` (needs two new compiler features), `buffer_n`/windowing, `join`,
  `delay`/full `distinct`/async-source merge/`sink`.
- **No remaining sub-projects** — brainstorming did not decompose this into
  multiple sub-projects; this single chain covered the whole request.
