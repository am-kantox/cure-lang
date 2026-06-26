# Std.Signal v3 + new Std.Sort module

**Date:** 2026-06-27
**Status:** Approved (design — operator pre-authorized an autonomous run)
**Builds on:** `2026-06-27-signal-combinators-v2-design.md` (v2, 13 combinators,
on branch `autopilot/std-signal`). v1+v2 give `Std.Signal` 30 combinators. This
spec adds a **new `Std.Sort` module** and **17 more `Std.Signal` combinators**,
chosen to close the windowed-memory, absence-detection, hysteresis, unit-delay,
and dt-aware-numerics gaps and to reach **Juniper feature-parity** (nothing Juniper's
Signal library has is left out: `record`→`sliding_window`, plus `join`, `edge`,
`sink`).

## 1. Goals

Two deliverables, built in order (the first is a prerequisite of the second):

1. **`Std.Sort` (new module, `lib/std/sort.cure`):** a small, pure,
   comparator-driven sort module headlined by **insertion sort**.
   `Std.Signal.moving_median` consumes it (rather than a private helper).
2. **`Std.Signal` v3 (17 combinators):** append to `lib/std/signal.cure`.

### Success criteria

- `Std.Sort` exists with the functions in §3, each verified by an ExUnit test
  in a new `test/cure/stdlib/cure_std_sort_test.exs`.
- Each §4 `Std.Signal` combinator exists in `lib/std/signal.cure` with the
  stated signature/semantics, verified in `test/cure/stdlib/cure_std_signal_test.exs`.
- No new language features; no FFI inside either module (the lone, deliberate
  exception is that `sink` *applies* a caller-supplied function whose body may
  be an `@extern` — `sink` itself stays pure plumbing; see §4e/§5).
- The full stdlib ExUnit suite stays green (no regression to v1+v2's 54 signal
  tests or the ~337 stdlib total).

## 2. Model (unchanged — restated so this spec stands alone)

A `Signal(A) = Sig(Option(A))` is "a value present or absent this tick."
Stateless combinators are pure `Signal -> Signal`. Stateful combinators take
prior state as an argument and **return new state in a tuple** alongside the
output signal (`%[output, new_state]`); the host threads state across ticks.
Time is passed in as an integer value (`now: Int`), never read from a clock.
Higher-order params of arity ≥2 are **curried** (`f: A -> B -> C`, applied
`f(a)(b)`). The unit value is `nil` (`Unit`). Runtime encodings for ExUnit
(verified across v1/v2): `Some(x)`→`{:some,x}`, `None()`→`{:none}`,
`Sig(Some(5))`→`{:sig,{:some,5}}`, Cure tuple `%[a,b]`→`{a,b}`, `Unit nil`→`nil`,
a `List` → an Erlang proper list (`[3,2,1]`), and a new sum type
`Either(A,B)` (§4e) → `Left(a)`→`{:left,a}`, `Right(b)`→`{:right,b}`.

## 3. `Std.Sort` (new module)

`mod Std.Sort`, group tag `fn __group__() -> Atom = :collections` (an accepted
group; auto-discovered by `Cure.Stdlib.Preload`'s compile-time scan of
`lib/std/*.cure`). Comparators are **curried** "less-or-equal" predicates
`le: A -> A -> Bool`, applied `le(a)(b)`. All functions pure.

| Function | Signature | Semantics |
|---|---|---|
| `insert` | `(le: A -> A -> Bool, x: A, xs: List(A)) -> List(A)` | insert `x` into already-`le`-sorted `xs`, keeping order. `[]`→`[x]`; otherwise place before the first `h` with `le(x)(h)` true |
| `insertion_sort` | `(le: A -> A -> Bool, xs: List(A)) -> List(A)` | sort by `le`: `[]`→`[]`; `[h\|t]`→`insert(le, h, insertion_sort(le, t))`. O(n²); intended for the small lists (sensor windows) this serves |
| `ascending` | `(xs: List(Int)) -> List(Int)` | `insertion_sort(fn(a) -> fn(b) -> a <= b, xs)` — Ints low→high |
| `descending` | `(xs: List(Int)) -> List(Int)` | `insertion_sort(fn(a) -> fn(b) -> a >= b, xs)` — Ints high→low |
| `sorted?` | `(le: A -> A -> Bool, xs: List(A)) -> Bool` | true iff `xs` is in non-decreasing `le` order (`?` predicate names are idiomatic here — cf. `Std.Refine.positive?`). Implemented via a private `local fn` walking adjacent pairs to avoid multi-element list patterns |

**Runtime encodings (ExUnit):** lists are Erlang lists. `ascending([3,1,2])` →
`[1,2,3]`; `descending([3,1,2])` → `[3,2,1]`; `insertion_sort(le, [])` → `[]`;
`sorted?(le, [1,2,2])` → `true`, `sorted?(le, [2,1])` → `false`. Generic
`insertion_sort` is tested with a curried `<=` passed from the test
(`fn a -> fn b -> a <= b end end`).

## 4. `Std.Signal` v3 combinators (17)

Signatures in Cure; capital type vars; stateful combinators return the built-in
`Tuple` (runtime `%[output, state]`). **Absent-tick convention (from v1):** a
`Sig(None())` input emits `Sig(None())` and returns state unchanged, except
where noted (`schmitt`, `sr_latch`, `timeout` are explicit about absence).

### 4a. Unit-delay & difference (pure shift register)

| Function | Signature | Semantics |
|---|---|---|
| `previous` | `(st: A, s: Signal(A)) -> Tuple` | one-(present)-tick delay: present `v` ⇒ emit `Sig(Some(st))` (the prior value) and new state `v`; absent ⇒ absent, state unchanged. Caller seeds `st` with the initial "previous". The missing primitive (Lustre `pre`) |
| `pairwise` | `(st: A, s: Signal(A)) -> Tuple` | present `v` ⇒ emit `Sig(Some(%[st, v]))` (prev,cur), new state `v`; absent ⇒ absent, unchanged |
| `diff` | `(st: Int, s: Signal(Int)) -> Tuple` | present `v` ⇒ emit `Sig(Some(v - st))`, new state `v`; absent ⇒ absent, unchanged. Discrete delta (per-sample; unitless — cf. dt-aware variants are out of scope here) |

Encodings: `previous(0, {:sig,{:some,5}})`→`{{:sig,{:some,0}},5}`;
`pairwise(0, {:sig,{:some,5}})`→`{{:sig,{:some,{0,5}}},5}`;
`diff(10, {:sig,{:some,13}})`→`{{:sig,{:some,3}},13}`.

### 4b. Windowed memory (bounded ring of capacity `n`)

State is `%[buf, len]` where `buf` is the last values **newest-first** (length
capped at `n`) and `len` is the current fill (capped at `n`). Seed `%[[], 0]`.
A private `take_n` truncates the pushed list to `n`; a private `imin` caps `len`.

| Function | Signature | Semantics |
|---|---|---|
| `sliding_window` | `(n: Int, st: Tuple, s: Signal(A)) -> Tuple` | present `v` ⇒ push (`buf2 = take_n([v\|buf], n)`, `len2 = imin(len+1, n)`); emit `Sig(Some(buf2))` **only once full** (`len2 >= n`), else absent; new state `%[buf2, len2]`. Absent ⇒ absent, unchanged. The foundational bounded-memory primitive (Juniper `record`) |
| `moving_average` | `(n: Int, st: Tuple, s: Signal(Int)) -> Tuple` | windowed mean with **graceful warm-up**: present `v` ⇒ push, emit `Sig(Some(sum(buf2) / len2))` every present tick (divides by current fill, so it works from tick 1), new state `%[buf2, len2]`. Absent ⇒ absent, unchanged. (`running_mean` is cumulative/all-time and goes stale; this tracks a drifting sensor) |
| `moving_median` | `(n: Int, st: Tuple, s: Signal(Int)) -> Tuple` | present `v` ⇒ push; **once full** emit `Sig(Some(Std.List.nth(Std.Sort.ascending(buf2), n / 2, 0)))`, else absent; new state `%[buf2, len2]`. Absent ⇒ absent, unchanged. Median rejects single-sample spikes without smearing edges (the only cheap filter that does) |

Encodings (n=3, seed `%[[],0]`): first push
`sliding_window(3, {[],0}, {:sig,{:some,1}})`→`{{:sig,{:none}},{[1],1}}`; once
full `sliding_window(3, {[2,1],2}, {:sig,{:some,3}})`→`{{:sig,{:some,[3,2,1]}},{[3,2,1],3}}`.
`moving_average(3, {[],0}, {:sig,{:some,1}})`→`{{:sig,{:some,1}},{[1],1}}` (1/1);
`moving_average(3, {[2,1],2}, {:sig,{:some,3}})`→`{{:sig,{:some,2}},{[3,2,1],3}}` (6/3).
`moving_median(3, {[5,5],2}, {:sig,{:some,100}})`→
`{{:sig,{:some,5}},{[100,5,5],3}}` (sorted `[5,5,100]`, index `3/2=1` ⇒ 5: spike
rejected). Before full, `moving_median(3, {[1],1}, {:sig,{:some,2}})`→
`{{:sig,{:none}},{[2,1],2}}`.

> **`Std.List.nth` note:** the plan must confirm the exact arity/signature of
> `Std.List.nth` (observed call shape `Std.List.nth(list, index, default)`); if
> it differs, fall back to a private `nth` helper in `signal.cure`. The sort,
> per the operator's instruction, MUST go through `Std.Sort` (not a local copy).

### 4c. Sensor filters

| Function | Signature | Semantics |
|---|---|---|
| `deadband` | `(tol: Int, st: Int, s: Signal(Int)) -> Tuple` | noise gate: present `v` with `iabs(v - st) > tol` ⇒ emit `Sig(Some(v))`, new state `v`; otherwise (within band) absent, state unchanged (still the last *emitted* value). Absent ⇒ absent, unchanged. (`drop_repeats` catches exact repeats; this catches near-repeats) |
| `low_pass` | `(k: Int, st: Int, s: Signal(Int)) -> Tuple` | integer IIR smoother: present `v` ⇒ `y = st + (v - st) / k`, emit `Sig(Some(y))`, new state `y`; absent ⇒ absent, unchanged. `k >= 1` (k=1 passes through). O(1) state, no buffer |

Encodings: `deadband(2, 10, {:sig,{:some,13}})`→`{{:sig,{:some,13}},13}`;
`deadband(2, 10, {:sig,{:some,11}})`→`{{:sig,{:none}},10}`;
`low_pass(2, 0, {:sig,{:some,100}})`→`{{:sig,{:some,50}},50}`. A private `iabs`
(absolute value) supports `deadband`.

### 4d. Control / logic

| Function | Signature | Semantics |
|---|---|---|
| `schmitt` | `(on_thr: Int, off_thr: Int, st: Bool, s: Signal(Int)) -> Tuple` | hysteresis comparator: present `v` ⇒ `v >= on_thr` true, `v <= off_thr` false, else **hold** `st`; emit `Sig(Some(out))` (a level — present every present tick), new state `out`. Absent ⇒ absent, unchanged. The correct analog→clean-bool (a single threshold chatters at the boundary) |
| `slew_limit` | `(max_step: Int, st: Int, s: Signal(Int)) -> Tuple` | output ramps toward input by ≤ `max_step`/tick: present `v` ⇒ `y = clampstep(v, st, max_step)`, emit `Sig(Some(y))`, new state `y`; absent ⇒ absent, unchanged. Protects actuators from step commands |
| `timeout` | `(window: Int, now: Int, st: Tuple, s: Signal(A)) -> Tuple` | watchdog / absence detector. State `%[last_seen, fired]` (Int, Bool). Present `_` ⇒ reset `%[now, false]`, emit absent. Absent ⇒ if `fired` already, absent + unchanged; else if `now - last_seen >= window` emit `Sig(Some(now - last_seen))` (the stale interval) once and set `fired`; else absent, unchanged. Seed `%[now0, false]`. The only way to detect "data stopped arriving" |
| `sr_latch` | `(st: Bool, set: Signal(A), reset: Signal(B)) -> Tuple` | reset-dominant set/reset latch (level output, present every tick): if `reset` present ⇒ `false`; else if `set` present ⇒ `true`; else hold `st`. Emit `Sig(Some(out))`, new state `out`. Latched alarms that stay asserted until acknowledged (`toggle` cannot) |

A private `clampstep(target, cur, step)` supports `slew_limit` (`target-cur>step`
⇒ `cur+step`; `cur-target>step` ⇒ `cur-step`; else `target`). `schmitt`,
`sr_latch` are **always-present** level outputs on a present/active tick (like
`constant`), distinct from the event combinators.

Encodings: `schmitt(70, 30, false, {:sig,{:some,80}})`→`{{:sig,{:some,true}},true}`;
hold `schmitt(70, 30, true, {:sig,{:some,50}})`→`{{:sig,{:some,true}},true}`; off
`schmitt(70, 30, true, {:sig,{:some,20}})`→`{{:sig,{:some,false}},false}`.
`slew_limit(5, 0, {:sig,{:some,100}})`→`{{:sig,{:some,5}},5}`.
`timeout(100, 50, {0, false}, {:sig,{:some,:x}})`→`{{:sig,{:none}},{50,false}}` (reset);
`timeout(100, 250, {100, false}, {:sig,{:none}})`→`{{:sig,{:some,150}},{100,true}}` (trip);
`timeout(100, 300, {100, true}, {:sig,{:none}})`→`{{:sig,{:none}},{100,true}}` (already fired).
`sr_latch(false, {:sig,{:some,:s}}, {:sig,{:none}})`→`{{:sig,{:some,true}},true}`;
reset-dominant `sr_latch(true, {:sig,{:some,:s}}, {:sig,{:some,:r}})`→`{{:sig,{:some,false}},false}`;
hold `sr_latch(true, {:sig,{:none}}, {:sig,{:none}})`→`{{:sig,{:some,true}},true}`.

### 4e. Juniper feature-parity (`join`, `edge`, `sink`)

| Function | Signature | Semantics |
|---|---|---|
| `join` | `(sa: Signal(A), sb: Signal(B)) -> Signal(Either(A, B))` | left-biased heterogeneous merge: `sa` present ⇒ `Sig(Some(Left(a)))`; else `sb` present ⇒ `Sig(Some(Right(b)))`; else absent. Requires a new public ADT `type Either(A, B) = Left(A) \| Right(B)` (declared in `signal.cure`; multi-constructor ADT syntax confirmed in-repo, cf. `Std.Access.Accessor`) |
| `edge` | `(prev: Bool, s: Signal(Bool)) -> Tuple` | emit `Sig(Some(nil))` (unit) on **any** transition of the present level: present `level` ⇒ if `level == prev` absent else unit pulse; new state `level`. Absent ⇒ absent, state unchanged. (Combines `rising_edge`+`falling_edge`) |
| `sink` | `(f: A -> Unit, s: Signal(A)) -> Unit` | terminal eliminator (the *output* bookend to `constant`/`never`): present `v` ⇒ `f(v)`; absent ⇒ `nil`. Returns `Unit`. `sink` itself is pure plumbing — the effect lives entirely in the caller's `f` (typically an `@extern`); it just enforces the present→apply / absent→skip contract in one place |

Encodings: `join({:sig,{:some,1}}, {:sig,{:none}})`→`{:sig,{:some,{:left,1}}}`;
`join({:sig,{:none}}, {:sig,{:some,2}})`→`{:sig,{:some,{:right,2}}}`;
both present (left-biased) `join({:sig,{:some,1}}, {:sig,{:some,2}})`→`{:sig,{:some,{:left,1}}}`;
both absent → `{:sig,{:none}}`. `edge(false, {:sig,{:some,true}})`→`{{:sig,{:some,nil}},true}`;
no change `edge(true, {:sig,{:some,true}})`→`{{:sig,{:none}},true}`;
absent `edge(false, {:sig,{:none}})`→`{{:sig,{:none}},false}`. `sink` is verified
by passing an `f` that records its argument as an Elixir side effect (e.g.
`fn x -> Process.put(:sunk, x); nil end`): assert the return is `nil` AND that
`f` ran on a present value but **not** on an absent one (`Process.get(:sunk)`).

### 4f. dt-aware numerics (exploit `now`)

Because ticks are irregular and `now` is passed as a value, the discrete
`running_sum`/`diff` give physically wrong units; these weight by the elapsed
interval Δt. Both carry a `primed` flag so the first sample (which has no Δt)
establishes the baseline without emitting a bogus number. Seed `%[0, 0, false]`.

| Function | Signature | Semantics |
|---|---|---|
| `integrate` | `(now: Int, st: Tuple, s: Signal(Int)) -> Tuple` | Σ x·Δt (left-rectangle). State `%[acc, last_now, primed]`. Present `v`: if not primed ⇒ emit `Sig(Some(acc))`, state `%[acc, now, true]` (no area yet); else `acc2 = acc + v * (now - last_now)`, emit `Sig(Some(acc2))`, state `%[acc2, now, true]`. Absent ⇒ absent, unchanged. (Coulomb counting, velocity-from-accel) |
| `derivative` | `(now: Int, st: Tuple, s: Signal(Int)) -> Tuple` | Δx/Δt (engineering-unit rate). State `%[last_val, last_now, primed]`. Present `v`: if not primed ⇒ emit absent, state `%[v, now, true]` (no rate yet); else if `now - last_now <= 0` ⇒ emit `Sig(Some(0))` (guard div-by-zero), state `%[v, now, true]`; else emit `Sig(Some((v - last_val) / (now - last_now)))`, state `%[v, now, true]`. Absent ⇒ absent, unchanged. (°C/s alarms, PID derivative term; distinct from `diff`, which is unitless per-sample) |

Encodings (seed `%[0, 0, false]` → `{0, 0, false}`):
`integrate(0, {0,0,false}, {:sig,{:some,5}})`→`{{:sig,{:some,0}},{0,0,true}}` (prime);
`integrate(10, {0,0,true}, {:sig,{:some,5}})`→`{{:sig,{:some,50}},{50,10,true}}` (5·10);
`integrate(20, {50,10,true}, {:sig,{:some,3}})`→`{{:sig,{:some,80}},{80,20,true}}` (50+3·10).
`derivative(0, {0,0,false}, {:sig,{:some,10}})`→`{{:sig,{:none}},{10,0,true}}` (prime);
`derivative(10, {10,0,true}, {:sig,{:some,30}})`→`{{:sig,{:some,2}},{30,10,true}}` ((30−10)/10).
Uses `*` (multiply) and `/` (truncating integer division).

## 5. Purity / dependencies

- `Std.Sort`: pure pattern-matching + curried comparators + `<=`/`>=`. No FFI.
- `Std.Signal` v3: pure pattern-matching, `pickup`, arithmetic (`+ - / ==
  >= <= > <`), `and`, list cons `[h|t]`, plus cross-module calls to
  `Std.Sort.ascending` and `Std.List.nth` (both pure) inside `moving_median`.
  Private helpers (`take_n`, `imin`, `iabs`, `clampstep`, `sig_present`,
  `sum_list`) via `local fn`. No `@extern` anywhere in the module.
- **`sink` is the one deliberate effect-shaped combinator** but remains pure
  itself: it never performs an effect, it only decides *whether* to call the
  `f` the caller supplied. The module stays FFI-free.

## 6. Verification

- `test/cure/stdlib/cure_std_sort_test.exs` (new): `insert`, `insertion_sort`
  (generic, curried `<=`), `ascending`, `descending`, `sorted?` (true and
  false), and the empty-list edge for each. `@sort :"Cure.Std.Sort"`,
  `setup_all` preloads `kind: :all`.
- `test/cure/stdlib/cure_std_signal_test.exs` (append): each §4 combinator —
  present path, absent path, and (stateful) two-tick state hand-off where
  meaningful; `sliding_window`/`moving_median` cover both pre-full (absent) and
  full (emit); `moving_average` covers warm-up; `schmitt` covers on/off/hold;
  `timeout` covers reset/trip/already-fired; `sr_latch` covers set/reset-
  dominance/hold; `join` covers left/right/both/neither; `edge` covers
  change/no-change/absent; `sink` covers effect-on-present / skip-on-absent +
  `nil` return; `integrate`/`derivative` cover the prime tick, a steady step,
  and (derivative) the `dt <= 0` guard.
- TDD loop (v1/v2's): write failing assertion → `mix test <file>` (red) →
  implement → rerun (green) → commit per task group. `mix test` recompiles the
  stdlib first. One build at a time. Stage 5 runs the whole `test/cure/stdlib/`
  suite once to confirm no regression.
- **v3 test assertions are immutable once written** (the v2 rule): make a red
  test green by changing the Cure implementation only — never by editing the
  assertion to match observed output. Sole exception: an assertion that is
  itself provably wrong (state why, then fix it).

## 7. Out of scope (truly out — and explicitly *not* anything Juniper has)

Per the operator's rule, **every** combinator in Juniper's Signal library is now
in scope and covered (`map, to_unit, meta, unmeta, constant, filter,
drop_repeats, merge, merge_all, join, map2, zip, unzip, foldp, record/
sliding_window, every, latch, toggle, rising_edge, falling_edge, edge, debounce
[parameterised — subsumes Juniper's fixed `debounce` + `debounceDelay`], sink`).

Still deferred, for the same model/purity reasons as v1/v2 (none are Juniper's):

- **Higher-order switching** — `switch`/`flatMap`/`mergeMap`/`switchMap`,
  Yampa `*Switch`/`par`, `flatten`/`join`-of-streams. Dynamic signal-of-signals
  is outside the per-tick first-order model. (Note: `join` *here* is the
  Either-merge of two signals, NOT monadic stream-flattening.)
- **Unbounded operators** — global `distinct`, `groupBy`, `toArray`,
  `reduce`/`last` (need a stream end or unbounded memory).
- **Wall-clock scheduling** — `interval`, time-shift `delay`, `bufferTime`
  (we have tick-driven `every`/`throttle`/`debounce`/`timeout`).
- **Windowed extrema, FIR**, `select`/`reset_on`, `take`/`drop`/`hold_for`,
  `debounce_count` — viable in-model but beyond this round's curated set;
  revisit on concrete need. (dt-aware `integrate`/`derivative` are now IN scope
  — §4f.)
