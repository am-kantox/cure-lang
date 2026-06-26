# Std.Signal — synchronous stream combinators for Cure

**Date:** 2026-06-26
**Status:** Approved (design)
**Context:** Concept harvested from the Juniper FRP language (`esp32-beam/Juniper/`).
Sibling note: `esp32-beam/docs/superpowers/specs/2026-06-26-juniper-capacity-types-parked.md`
parks the other Juniper idea (capacity types). This spec pursues the signal/stream
idea (#1) and its embedded timer/edge combinators (#3).

## 1. Goal

Add `Std.Signal`, a **pure, synchronous, allocation-light stream-combinator
library** to the Cure standard library (`cure-lang/lib/std/signal.cure`, compiled
to `Cure.Std.Signal`). It gives Cure programs a composable vocabulary for
transforming streams of events — `map`/`filter`/`merge` plus the stateful
`foldp`/`dropRepeats`/`debounce`/`every`/edge-detect — that today must be
hand-rolled inside every actor that reacts to sensor or message streams.

This is the part of Juniper's model that Cure genuinely lacks. Cure already has
the *stateful fold* as a first-class construct (an FSM's `on_transition` ≡
Juniper's `foldP`); what is missing is the **upstream pure combinator algebra**
that shapes the event stream feeding such a fold.

### Success criteria

- `Std.Signal` compiles as part of `cure stdlib` with no new language features.
- Every combinator listed in §4 exists with the stated signature and semantics,
  verified by an ExUnit test (`test/cure/stdlib/cure_std_signal_test.exs`)
  following the existing pure-Cure stdlib test pattern (see §6).
- A worked driver demo (`examples/signal_sensor.cure`) shows the canonical
  integration: a pipeline `debounce → dropRepeats → foldp` hosted inside one
  process, feeding a small FSM, runnable on generic-unix AtomVM.

## 2. The model (settled in brainstorming)

A signal is **"a value present or absent this tick"**:

```cure
type Signal(a) = Sig(Option(a))
```

Three roles, deliberately separated:

- **The combinators are pure synchronous data transforms — NOT a graph of
  processes.** One tick = one synchronous pass through the pipeline. This
  preserves Juniper's core virtue (no runtime reactive graph, no glitches) and
  is what keeps it cheap on AtomVM (process count and memory are scarce). We
  explicitly reject process-per-combinator.
- **The actor is the host/driver, not the implementation of a node.** One
  process hosts one pipeline; its **mailbox is the tick** (each received message
  runs the pipeline once); its `data` record holds the stateful combinators'
  state. We explicitly reject "model each combinator on an actor."
- **The FSM is a consumer, not the substrate.** `foldp ≡ on_transition`, but an
  FSM is shaped around *named discrete modes* (locked/unlocked); running-average
  and debounce are not modes. The signal pipeline shapes the stream and hands
  clean events to an FSM where real modes exist. We explicitly reject "model
  signals on FSM."

### State without `inout`

Cure has no `inout` (BEAM values are immutable), so Juniper's in-place state
mutation becomes **state-in / state-out**. Stateless combinators are pure
`Signal(a) -> Signal(b)`. Stateful combinators take prior state as an argument
and **return new state in a tuple** alongside the output signal:

```
stateless:  fn map(f, s: Signal(a)) -> Signal(b)
stateful:   fn dropRepeats(prev: Option(a), s: Signal(a)) -> %[Signal(a), Option(a)]
                                                              #  ^output      ^new state
```

The host actor stores each stateful combinator's state in its `data` record and
threads it each tick. This is explicit (no auto-threading like an arrowized
`>>>`); that is the accepted v1 trade — readable and trivially testable. A
state-bundling `Pipeline` helper is deferred (YAGNI) — see §7.

### Time is a value, not an effect

The timer/edge combinators (§4c) need the current time, but to keep every
combinator **pure and testable** the caller passes the current timestamp in as a
parameter (`now: Int`, milliseconds). The host reads the clock once per tick
(`Std.Time.now` / `:erlang.monotonic_time`) and passes it down. Tests supply
synthetic timestamps. `Std.Signal` therefore needs **no FFI** and is 100% pure
Cure.

## 3. Relationship to existing stdlib

- Distinct from `Std.Iter` (pull-based, finite/lazy sequences). `Std.Signal` is
  push-based, time-indexed, unbounded-stream-shaped. No overlap.
- Uses `Std.Option` (`Some`/`None`) for the present/absent value and for
  `dropRepeats` history.
- The demo uses an `actor` (host) and an `fsm` (consumer); both already work on
  AtomVM (proven in phases 3/3.5).

## 4. API surface (v1 scope)

Names follow Cure stdlib conventions. Signatures use Cure syntax. `Signal(a)`
is `Sig(Option(a))`. Higher-order params of arity ≥2 are curried at the BEAM
boundary (matches `Std.Iter`); arity-1 params are plain.

### 4a. Stateless (pure `Signal -> Signal`)

| Function | Signature | Semantics |
|---|---|---|
| `constant` | `(v: a) -> Signal(a)` | always-present signal of `v` (`Sig(Some(v))`) |
| `never` | `() -> Signal(a)` | always-absent (`Sig(None)`) |
| `map` | `(f: (a) -> b, s: Signal(a)) -> Signal(b)` | apply `f` when present, else absent |
| `filterS` | `(p: (a) -> Bool, s: Signal(a)) -> Signal(a)` | keep value when `p` is **true**, else absent |
| `reject` | `(p: (a) -> Bool, s: Signal(a)) -> Signal(a)` | inverse of `filterS` |
| `merge` | `(a: Signal(a), b: Signal(a)) -> Signal(a)` | left-biased: `a` if present, else `b` |
| `mapTo` | `(v: b, s: Signal(a)) -> Signal(b)` | replace present value with constant `v` |
| `toUnit` | `(s: Signal(a)) -> Signal(Unit)` | `mapTo(())` |

> **Naming note:** the keep-when-true combinator is `filterS` (not `filter`) to
> avoid colliding with / being confused for `Std.List.filter`, and because
> Juniper's own `filter` has the *opposite* (filter-out-when-true) sense — we do
> not replicate that footgun. `reject` is the filter-out direction, named
> explicitly.

### 4b. Stateful (state-in / state-out, return `%[Signal(_), state]`)

| Function | Signature | Semantics |
|---|---|---|
| `foldp` | `(f: (a, s) -> s, st: s, sig: Signal(a)) -> %[Signal(s), s]` | fold over the past: when present, `st' = f(val, st)`, emit `st'`; when absent, emit absent and keep `st` |
| `dropRepeats` | `(prev: Option(a), sig: Signal(a)) -> %[Signal(a), Option(a)]` | suppress a value equal to the previous emitted value |
| `latch` | `(prev: a, sig: Signal(a)) -> %[Signal(a), a]` | emit incoming when present (and remember it); when absent, re-emit last remembered |
| `count` | `(n: Int, sig: Signal(a)) -> %[Signal(Int), Int]` | running count of present ticks |

`foldp` is the load-bearing primitive; `dropRepeats`/`latch`/`count` are defined
in terms of it where natural.

### 4c. Timer + edge (embedded sweet spot — #3)

These take `now: Int` (ms) as a value (§2). State lives in records defined in the
module.

| Function | Signature | Semantics |
|---|---|---|
| `every` | `(interval: Int, now: Int, last: Int) -> %[Signal(Int), Int]` | emit `now` at most once per `interval`-ms window; state is the last-pulse timestamp |
| `risingEdge` | `(prev: Bool, sig: Signal(Bool)) -> %[Signal(Unit), Bool]` | emit unit on a false→true transition of the present level |
| `fallingEdge` | `(prev: Bool, sig: Signal(Bool)) -> %[Signal(Unit), Bool]` | emit unit on a true→false transition |
| `debounce` | `(interval: Int, now: Int, st: Debounce(a), sig: Signal(a)) -> %[Signal(a), Debounce(a)]` | emit a value only after it has been stable for `interval` ms; state holds the pending candidate + its first-seen timestamp |

`Debounce(a)` is a record defined in the module (candidate `Option(a)` + `since:
Int`). Exact fields finalized in the plan; behavior is the contract.

### Out of v1 scope (YAGNI)

`zip`/`map2`, `join`, `mergeMany`, `record`, `toggle`, `sample`, `throttle`,
`unzip`, `meta`/`unmeta`. They are real but not needed to prove #1+#3 and each
adds state-threading surface. Revisit after v1 lands.

## 5. Components & boundaries

- **`lib/std/signal.cure`** — the module. One job: pure stream combinators.
  Depends only on `Std.Option` (and `Std.List`/equality as needed for
  `dropRepeats`). Nothing depends on it.
- **`examples/signal_sensor.cure`** — the integration demo (host actor + FSM
  consumer). Depends on `Std.Signal`; demonstrates, does not extend.
- **`test/cure/stdlib/cure_std_signal_test.exs`** — the executable spec.

Each combinator is independently testable: given an input `Signal` (and state),
assert the output `Signal` (and new state). No combinator reads global state.

## 6. Verification strategy (the TDD harness — grounded in the repo)

Pure-Cure stdlib modules in this repo are tested with **ExUnit `.exs`** files
that call the compiled module by its runtime atom after preloading. Confirmed
against `test/cure/stdlib/iter_test.exs` (43 tests, passing on the worktree
baseline):

```elixir
@sig :"Cure.Std.Signal"
setup_all do
  Cure.Stdlib.Preload.preload(examples: false, kind: :all)
  :ok
end
```

**Runtime value encoding (confirmed from `iter_test.exs`):**

- ADT constructors → tagged tuples: `Some(x)` → `{:some, x}`, `None` → `{:none}`,
  so `Sig(Some(5))` → `{:sig, {:some, 5}}` and `Sig(None)` → `{:sig, {:none}}`.
- Cure tuple `%[a, b]` → Erlang `{a, b}`, so a `%[Signal(s), s]` return →
  `{{:sig, {:some, v}}, s}`.
- Higher-order params of arity ≥2 are **curried** (`fn a -> fn b -> ... end
  end`); arity-1 params are plain `fn a -> ... end`.

**TDD loop per task (confirmed on the worktree baseline):** `mix test` *itself
recompiles the whole stdlib from `lib/std/*.cure` before running ExUnit* (the
"34 compiled / Escript built" step observed before the suite runs). So the loop
is simply: write a failing assertion in `cure_std_signal_test.exs` (red —
undefined function / wrong output), implement the combinator in `signal.cure`,
run `mix test test/cure/stdlib/cure_std_signal_test.exs` (green). No separate
stdlib-recompile step is needed — this is why R3 below is resolved.

**On-AtomVM check (closing evidence, not the TDD driver):** the
`examples/signal_sensor.cure` demo is run on generic-unix AtomVM via the
esp32-beam harness pattern (`phase35/run-on-unix.sh`), printing an observable
line, to confirm the combinators behave identically on the target VM. This is a
single confirmatory run, not part of the red-green loop.

Each combinator's tests cover: present-input path, absent-input path, and (for
stateful) correct state hand-off across two consecutive ticks. Timer/edge
combinators are driven with synthetic `now`/level sequences.

## 7. Risks & open questions

- **R1 — Curried HOF boundary.** If `foldp`'s `f: (a, s) -> s` is *not* curried
  the way `Std.Iter.fold` is, test call shape differs. *Mitigation:* the very
  first `foldp` test pins the calling convention; adjust once, centrally.
- **R2 — `dropRepeats` equality.** Requires value equality on `a`. Cure compares
  via structural equality (`==`); confirm it works for the demo's value type.
  *Acceptable:* v1 demo uses `Int`.
- **R3 — Stdlib recompile in the test loop. [RESOLVED on worktree baseline].**
  `mix test` recompiles the stdlib (incl. `signal.cure`) before each run, so the
  edit→test loop is one step. No special handling needed.
- **Open — state-threading ergonomics.** Chaining several *stateful* stages
  means threading each one's state through the host's `data` by hand. Accepted
  for v1; a `Pipeline` state-bundle helper is a candidate v2 follow-up, captured
  here so it is not silently dropped.

## 8. Out of scope

- A reactive runtime / dependency graph (rejected by design — §2).
- Process-per-combinator (rejected — §2).
- Capacity/bounded-buffer types (parked — sibling spec).
- The v2 combinators and `Pipeline` helper listed in §4 / §7.
- Hardware (real ESP32) flashing — generic-unix AtomVM is the verification VM;
  on-hardware is a later, separate step if desired.
