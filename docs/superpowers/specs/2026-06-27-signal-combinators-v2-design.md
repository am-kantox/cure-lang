# Std.Signal v2 — more combinators + variadic-merge feasibility

**Date:** 2026-06-27
**Status:** Approved (design — operator pre-authorized an autonomous run)
**Builds on:** `2026-06-26-std-signal-design.md` (v1, 17 combinators, on branch
`autopilot/std-signal`). This spec adds the v2 combinator set to the same
`lib/std/signal.cure` and answers the dependent-variadic-merge question.

## 1. Goal

Two deliverables:

1. **Research finding (§3):** can Cure express a *dependently-typed variadic*
   `merge` (arity as a parameter) that specializes to fixed-arity BEAM
   functions? Answer, with compiler evidence: **no, not today** — so the N-ary
   merge ships as the **list form** `merge_all(List(Signal(A)))`.
2. **v2 combinators (§4):** 13 new combinators closing the expressive gaps
   identified after v1 (multi-stream combination, map-filter, rate-limiting,
   sampling, splitting, and sensor-oriented accumulation), all obeying the v1
   model — pure, synchronous, state-in/state-out, FFI-free.

### Success criteria

- Each §4 combinator exists in `lib/std/signal.cure` with the stated signature
  and semantics, verified by an ExUnit test in
  `test/cure/stdlib/cure_std_signal_test.exs` (same harness as v1).
- No new language features; no FFI (Std.Signal stays 100% pure Cure — confirmed
  in §5 that integer division `/` and `Std.Option`/`Std.List` cover every need).
- The full stdlib ExUnit suite stays green (no regressions to v1's 35 tests).

## 2. Model (unchanged from v1 — restated so this spec stands alone)

A `Signal(A) = Sig(Option(A))` is "a value present or absent this tick."
Stateless combinators are pure `Signal -> Signal`. Stateful combinators take
prior state as an argument and **return new state in a tuple** alongside the
output signal (Cure has no `inout`); the host threads that state across ticks.
Higher-order params of arity ≥2 are **curried** (`f: A -> B -> C`, applied
`f(a)(b)`), matching v1's `foldp` and `lib/std/list.cure`. Runtime encodings for
ExUnit assertions (verified in v1): `Some(x)`→`{:some,x}`, `None()`→`{:none}`,
`Sig(Some(5))`→`{:sig,{:some,5}}`, tuple `%[a,b]`→`{a,b}`, `Unit` `nil`→`nil`.

## 3. Research finding — dependently-typed variadic merge is not feasible today

The question: rather than `merge_all(List)`, could Cure's dependent types express
a true variadic `merge(a, b, c, …)` whose arity is a parameter, specialized to
fixed-arity BEAM `merge/2`, `merge/3`, …? A dependently-typed language can in
principle (the `printf` construction): a type-level function builds the curried
arrow chain —

```
fn MergeFn(n: Nat) -> Type =
  match n
    zero    -> Signal(A)
    succ(k) -> Signal(A) -> MergeFn(k)
fn merge_n(n: Nat) -> MergeFn(n) = ...
```

**Two independent compiler facts make this infeasible in Cure today** (evidenced
by source inspection; cited so a reviewer can re-verify):

- **No large elimination / type-level `Nat -> Type` recursion.** Cure has no
  `Type` universe — `Type.resolve_name/1`'s known set is `Int, Float, …, Pid`
  with no `Type`/`Set`/`Prop` sort (`lib/cure/types/type.ex:407-420`). Type-level
  computation is only the closed arithmetic/boolean fold in
  `Cure.Types.Reduce` (`lib/cure/types/reduce.ex:127-147, 169-219`): `+ - * / %`,
  booleans, literal comparisons, `fst/snd` — **no user-function evaluation**. A
  `match`/`if` in a return-type position has no `Type.resolve/1` clause and falls
  to `def resolve(_), do: :any` (`type.ex:399`), so `MergeFn(n) -> Type` collapses
  to `:any`. Type-level pattern matching is explicitly reserved/out-of-scope
  (`docs/MATCH.md:1541-1556, 1630-1633`), and Pi types are not yet surfaced in
  source syntax (`examples/length_indexed.cure:7-9`). The construction cannot be
  written or checked.
- **Monomorphization is type-keyed and arity-preserving.** The pass keys only on
  `{:type_var, _}` substitutions, never on values/Nats
  (`lib/cure/optimizer/monomorphise.ex:182-198, 278-393`), and clones each
  specialization's `:params` verbatim (`materialise_specialisations`, lines
  583-614) — so one source function can never yield clones of differing arity.
  (Codegen *does* emit honest fixed-arity BEAM functions — ground-truthed: the
  compiled `Cure.Std.Pair.beam` exports a real `{map_both,3}` — so only a *new*
  arity-directed expansion pass, which does not exist, would be needed.)

**Closest expressible thing** is the list/vector form (`n` as a type *index*, not
a driver of large elimination), which is exactly `merge_all`. **Decision:** ship
`merge_all(List(Signal(A)))`. A true variadic `merge` would require two new
compiler features (large elimination + arity-directed monomorphization) and is
recorded here as out of scope.

## 4. v2 combinator set

Signatures in Cure syntax; capital type vars; stateful combinators return the
built-in `Tuple` (runtime shape shown as `%[output, state]`). Curried HOF params
noted. **Absent-tick convention (from v1):** on a `Sig(None())` input every
stateful combinator emits `Sig(None())` and returns state unchanged, except where
noted.

### 4a. Stateless (pure)

| Function | Signature | Semantics |
|---|---|---|
| `merge_all` | `(sigs: List(Signal(A))) -> Signal(A)` | left-biased N-ary merge: the first present signal in the list, else absent; `[]` → absent |
| `filter_map` | `(f: A -> Option(B), s: Signal(A)) -> Signal(B)` | map then keep only `Some`: present `v` → `f(v)` is `Some(b)` ⇒ `Sig(Some(b))`, `None()` ⇒ absent |
| `unzip` | `(s: Signal(Tuple)) -> Tuple` | split a tuple-signal: present `%[a,b]` → `%[Sig(Some(a)), Sig(Some(b))]`; absent → `%[Sig(None()), Sig(None())]` |
| `partition` | `(p: A -> Bool, s: Signal(A)) -> Tuple` | present `v` → `%[matching, non-matching]`: `p(v)` ⇒ `%[Sig(Some(v)), Sig(None())]`, else `%[Sig(None()), Sig(Some(v))]`; absent → both absent |
| `sample` | `(held: A, trigger: Signal(B)) -> Signal(A)` | emit the `held` value whenever `trigger` is present, else absent (event×behavior sampling; the host threads `held`, e.g. via `latch`) |
| `meta` | `(s: Signal(A)) -> Signal(Option(A))` | reify presence as an always-present signal: present `v` → `Sig(Some(Some(v)))`, absent → `Sig(Some(None()))` |
| `unmeta` | `(s: Signal(Option(A))) -> Signal(A)` | inverse of `meta`: `Sig(Some(Some(v)))` → `Sig(Some(v))`; `Sig(Some(None()))` and `Sig(None())` → absent |

### 4b. Stateful (state-in / state-out)

| Function | Signature | Semantics |
|---|---|---|
| `map2` | `(f: A -> B -> C, st: Tuple, sa: Signal(A), sb: Signal(B)) -> Tuple` | combine two streams (a.k.a. `combine_latest`): state `%[lastA, lastB]`; each present value updates its slot; emit `f(na)(nb)` if **either** input is present this tick, else absent; new state `%[na, nb]`. Caller seeds `%[a0, b0]` |
| `zip` | `(st: Tuple, sa: Signal(A), sb: Signal(B)) -> Tuple` | `map2` with tupling: emits `Sig(Some(%[na, nb]))` when either is present; same `%[lastA,lastB]` state |
| `throttle` | `(interval: Int, now: Int, last_emit: Int, s: Signal(A)) -> Tuple` | **leading-edge** rate-limit: present `v` with `now - last_emit >= interval` ⇒ emit `Sig(Some(v))`, new state `now`; otherwise absent, state unchanged. Caller seeds `last_emit` (e.g. `now - interval`) so the first eligible value fires. (Complements v1 `debounce`, which is trailing-edge.) |
| `toggle` | `(a: A, b: A, st: A, trigger: Signal(C)) -> Tuple` | on each present `trigger`, flip: `nv = (st == a) ? b : a`; emit `Sig(Some(nv))`, new state `nv`. Caller seeds `st` with `a` or `b`. Absent → absent, state unchanged |
| `running_sum` | `(st: Int, s: Signal(Int)) -> Tuple` | running total: present `v` → emit `Sig(Some(st+v))`, new state `st+v` |
| `running_mean` | `(st: Tuple, s: Signal(Int)) -> Tuple` | moving average: state `%[sum, count]`; present `v` → `sum2=sum+v`, `cnt2=count+1`, emit `Sig(Some(sum2 / cnt2))` (integer division; `cnt2 ≥ 1`), new state `%[sum2, cnt2]`. Caller seeds `%[0, 0]` |

### Notes
- `combine_latest` (RxJS) **is** `map2`; `zip` here is the latest-pair form. No
  separate `combine_latest` function.
- `running_sum` overlaps `foldp(+)` but is a zero-friction convenience for the
  most common numeric fold; `running_mean` is the genuinely useful sensor helper
  (v1's demo hand-rolled an accumulator — the tell).
- `sample` shares v1 `map_to`'s one-line body (`Sig(Some(_))` → emit the held
  value, absent → absent); it earns a distinct name as the FRP sample-and-hold
  idiom (host threads `held` via `latch`), not as new expressive power.

## 5. Purity / dependencies (confirming "no FFI")

Every v2 combinator is pure Cure: pattern-matching, `pickup`, `==`, `+`, and
integer `/` (verified: `/` on `Int` operands yields `Int` — `lib/std/math.cure`
`safe_div` is `a / b -> Int`; `running_mean` only divides when `count ≥ 1`, so no
divide-by-zero). Uses `Std.Option`/`Std.List` only. No `@extern`. Std.Signal
remains 100% pure Cure, as v1 promised.

## 6. Verification

Append v2 tests to `test/cure/stdlib/cure_std_signal_test.exs` (one `describe`
block per task group), asserting in the v1 runtime encoding. Each combinator
covers: present path, absent path, and (stateful) correct state hand-off across
two consecutive ticks; `map2`/`zip` cover "fire on either / remember the other";
`throttle` covers the interval boundary; `toggle` covers the flip; `running_mean`
covers truncating integer division. TDD loop is v1's: write failing assertion →
`mix test test/cure/stdlib/cure_std_signal_test.exs` (red) → implement → rerun
(green) → commit. `mix test` recompiles the stdlib first. No new example program
is needed — v1's `signal_sensor.cure` already proves runnable integration; v2's
surface is verified by unit tests. Stage 5 runs the whole `test/cure/stdlib/`
suite once to confirm no regression.

## 7. Out of scope (deferred, with reasons)

- **True variadic dependent `merge`** — needs large elimination +
  arity-directed monomorphization (§3); not available.
- **`buffer_n` / windowing** — bounded-list truncation is fiddlier; defer until a
  concrete need. (`record`/unbounded buffering is rejected — unbounded memory is
  hostile to AtomVM.)
- **`join` (→ `Signal(Either)`)** — `zip`/`map2` cover two-stream combination;
  add only if an `Either`/`Result`-typed join is specifically wanted.
- **`delay`, full `distinct`, async-source merge, `sink`/`tap`** — rejected in v1
  for model/purity reasons (delay needs scheduling; full distinct is unbounded
  memory; async merge is the mailbox's job; effectful terminals belong to the
  host). Unchanged here.
