# Std.Signal Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add `Std.Signal`, a pure synchronous stream-combinator library, to the Cure standard library, verified by ExUnit tests and a runnable demo.

**Architecture:** A single pure-Cure module `lib/std/signal.cure` (compiles to runtime atom `Cure.Std.Signal`) defining `type Signal(A) = Sig(Option(A))` plus stateless combinators (`Signal -> Signal`) and stateful combinators (state-in / state-out, returning a `%[output_signal, new_state]` tuple). Tests are an ExUnit `.exs` file calling the compiled module by atom after preloading the stdlib, exactly mirroring `test/cure/stdlib/iter_test.exs`. A worked `examples/signal_sensor.cure` demonstrates the pipeline feeding a small FSM.

**Tech Stack:** Cure (dependently-typed BEAM language), Elixir/ExUnit (test harness), `mix` (build + test).

**Source spec:** `docs/superpowers/specs/2026-06-26-std-signal-design.md` (hardened). Read §2 (model), §4 (API), §6 (verification) before starting.

## Global Constraints

These apply to EVERY task — copied verbatim from the spec and from verified codebase conventions:

- **No new language features.** Pure-Cure stdlib module only.
- **Module header:** `mod Std.Signal`, with `fn __group__() -> Atom = :signal` as the first function (Preload group tag, mirrors every other `lib/std/*.cure`).
- **Type variables are capital letters** (`A`, `B`, `S`); lowercase in type position names a concrete type (Cure rule).
- **Nullary ADT constructors are matched/built with `()`:** `None()`, never bare `None`.
- **Signal type:** `type Signal(A) = Sig(Option(A))`. `Option`/`Some`/`None` are globally available from `Std.Core` (mirrors `lib/std/option.cure`, which uses them with no import). If Task 1's first compile reports `Option`/`Some`/`Sig` unresolved, add `use Std.Core` — but do not add it preemptively.
- **Stateful combinators return the Cure built-in `Tuple`** type; the `%[output, state]` form is the runtime tuple shape (convention from `lib/std/pair.cure`).
- **Higher-order params are curried** at arity ≥2: a folder is typed `f: A -> S -> S` and applied `f(v)(st)` (verified in `lib/std/list.cure` foldl). Arity-1 HOF params are plain (`f: A -> B`, applied `f(v)`).
- **Runtime value encoding (for ExUnit assertions), verified from `iter_test.exs`:** `Some(x)` → `{:some, x}`; `None()` → `{:none}`; `Sig(Some(5))` → `{:sig, {:some, 5}}`; `Sig(None())` → `{:sig, {:none}}`; Cure tuple `%[a, b]` → `{a, b}`; Cure `Unit` value `nil` → Erlang `nil`. So a `%[Signal(S), S]` return is `{{:sig, {:some, v}}, s}`.
- **Absent-tick convention (spec §4b):** on a `Sig(None())` input, every stateful combinator emits `Sig(None())` and returns its state UNCHANGED, EXCEPT `latch` (re-emits remembered value). `every`/`constant`/`never` take no input signal.
- **TDD per task:** write failing ExUnit test → run `mix test test/cure/stdlib/cure_std_signal_test.exs` (red) → implement in `signal.cure` → rerun (green) → commit. `mix test` recompiles the stdlib (incl. `signal.cure`) automatically before running — no separate compile step. Tests are behavioral and immutable: once written and passing, a later task MUST NOT edit an earlier task's assertions to make new code pass.
- **All git ops run inside the worktree** so commits land on `autopilot/std-signal`.
- **Run only one `mix test` at a time** (never concurrent suites).

---

### Task 1: Module scaffold + `Signal` type + sources (`constant`, `never`)

This task proves the whole harness end-to-end: the module compiles into the stdlib, Preload loads `Cure.Std.Signal`, and the runtime encoding is as expected. Everything else builds on it.

**Files:**
- Create: `lib/std/signal.cure`
- Create: `test/cure/stdlib/cure_std_signal_test.exs`

**Interfaces:**
- Produces: `Cure.Std.Signal.constant/1`, `Cure.Std.Signal.never/0`; the `Signal(A) = Sig(Option(A))` type used by every later task.

- [ ] **Step 1: Write the failing test file**

Create `test/cure/stdlib/cure_std_signal_test.exs`:

```elixir
defmodule Cure.Stdlib.SignalTest do
  use ExUnit.Case, async: false

  # `Cure.Std.Signal` is loaded dynamically by `Cure.Stdlib.Preload` in
  # `setup_all`; silence the compile-time "module not available" warning.
  @compile {:no_warn_undefined, :"Cure.Std.Signal"}
  @sig :"Cure.Std.Signal"

  setup_all do
    Cure.Stdlib.Preload.preload(examples: false, kind: :all)
    :ok
  end

  describe "sources" do
    test "constant/1 is an always-present signal" do
      assert @sig.constant(5) == {:sig, {:some, 5}}
    end

    test "never/0 is an always-absent signal" do
      assert @sig.never() == {:sig, {:none}}
    end
  end
end
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: FAIL — `signal.cure` does not exist yet, so `Cure.Std.Signal` is undefined (`UndefinedFunctionError` / module not available).

- [ ] **Step 3: Write the minimal module**

Create `lib/std/signal.cure`:

```cure
mod Std.Signal
  ## Synchronous stream combinators. A `Signal(A)` is "a value present or
  ## absent this tick": `Sig(Some(v))` or `Sig(None())`. Stateless
  ## combinators are pure `Signal -> Signal`; stateful ones take prior
  ## state and return `%[output_signal, new_state]`. See the design spec
  ## at docs/superpowers/specs/2026-06-26-std-signal-design.md.

  ## Group tag consumed by `Cure.Stdlib.Preload`.
  fn __group__() -> Atom = :signal

  ## A value present or absent this tick.
  type Signal(A) = Sig(Option(A))

  ## Always-present signal carrying `v`.
  fn constant(v: A) -> Signal(A) = Sig(Some(v))

  ## Always-absent signal.
  fn never() -> Signal(A) = Sig(None())
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: PASS (2 tests). If it fails with an unresolved `Option`/`Some`/`Sig`, add `use Std.Core` under the `mod Std.Signal` line and rerun.

- [ ] **Step 5: Commit**

```bash
git add lib/std/signal.cure test/cure/stdlib/cure_std_signal_test.exs
git commit -m "feat(std-signal): module scaffold, Signal type, constant/never"
```

---

### Task 2: Stateless value maps (`map`, `mapTo`, `toUnit`)

**Files:**
- Modify: `lib/std/signal.cure`
- Modify: `test/cure/stdlib/cure_std_signal_test.exs`

**Interfaces:**
- Consumes: `Signal(A)` (Task 1).
- Produces: `map/2` (`f: A -> B` first, signal second), `mapTo/2`, `toUnit/1`.

- [ ] **Step 1: Write the failing tests** — append inside the test module:

```elixir
  describe "map / mapTo / toUnit" do
    test "map applies f to a present value" do
      assert @sig.map(fn x -> x * 2 end, {:sig, {:some, 5}}) == {:sig, {:some, 10}}
    end

    test "map preserves absence" do
      assert @sig.map(fn x -> x * 2 end, {:sig, {:none}}) == {:sig, {:none}}
    end

    test "mapTo replaces a present value with a constant" do
      assert @sig.mapTo(:hit, {:sig, {:some, 99}}) == {:sig, {:some, :hit}}
      assert @sig.mapTo(:hit, {:sig, {:none}}) == {:sig, {:none}}
    end

    test "toUnit maps a present value to the unit value nil" do
      assert @sig.toUnit({:sig, {:some, 7}}) == {:sig, {:some, nil}}
      assert @sig.toUnit({:sig, {:none}}) == {:sig, {:none}}
    end
  end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: FAIL — `map`/`mapTo`/`toUnit` undefined.

- [ ] **Step 3: Implement** — append to `lib/std/signal.cure`:

```cure
  ## Apply `f` to the value when present; preserve absence.
  fn map(f: A -> B, s: Signal(A)) -> Signal(B) =
    match s
      Sig(Some(v)) -> Sig(Some(f(v)))
      Sig(None()) -> Sig(None())

  ## Replace a present value with the constant `v`; preserve absence.
  fn mapTo(v: B, s: Signal(A)) -> Signal(B) =
    match s
      Sig(Some(_)) -> Sig(Some(v))
      Sig(None()) -> Sig(None())

  ## Collapse a present value to the unit value; preserve absence.
  fn toUnit(s: Signal(A)) -> Signal(Unit) = mapTo(nil, s)
```

- [ ] **Step 4: Run to verify pass**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: PASS (6 tests).

- [ ] **Step 5: Commit**

```bash
git add lib/std/signal.cure test/cure/stdlib/cure_std_signal_test.exs
git commit -m "feat(std-signal): map, mapTo, toUnit"
```

---

### Task 3: Stateless filters and merge (`filterS`, `reject`, `merge`)

**Files:**
- Modify: `lib/std/signal.cure`
- Modify: `test/cure/stdlib/cure_std_signal_test.exs`

**Interfaces:**
- Consumes: `Signal(A)` (Task 1).
- Produces: `filterS/2` (`p: A -> Bool` first, signal second), `reject/2`, `merge/2`.

- [ ] **Step 1: Write the failing tests** — append:

```elixir
  describe "filterS / reject / merge" do
    test "filterS keeps a value when the predicate is true" do
      assert @sig.filterS(fn x -> x > 3 end, {:sig, {:some, 5}}) == {:sig, {:some, 5}}
    end

    test "filterS drops a value when the predicate is false" do
      assert @sig.filterS(fn x -> x > 3 end, {:sig, {:some, 1}}) == {:sig, {:none}}
    end

    test "reject is the inverse of filterS" do
      assert @sig.reject(fn x -> x > 3 end, {:sig, {:some, 5}}) == {:sig, {:none}}
      assert @sig.reject(fn x -> x > 3 end, {:sig, {:some, 1}}) == {:sig, {:some, 1}}
    end

    test "merge is left-biased" do
      assert @sig.merge({:sig, {:some, 1}}, {:sig, {:some, 2}}) == {:sig, {:some, 1}}
      assert @sig.merge({:sig, {:none}}, {:sig, {:some, 2}}) == {:sig, {:some, 2}}
      assert @sig.merge({:sig, {:none}}, {:sig, {:none}}) == {:sig, {:none}}
    end
  end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: FAIL — `filterS`/`reject`/`merge` undefined.

- [ ] **Step 3: Implement** — append to `lib/std/signal.cure`:

```cure
  ## Keep the value when `p` is true, else drop to absent.
  fn filterS(p: A -> Bool, s: Signal(A)) -> Signal(A) =
    match s
      Sig(Some(v)) ->
        pickup
          p(v) -> Sig(Some(v))
          else -> Sig(None())
      Sig(None()) -> Sig(None())

  ## Drop the value when `p` is true, else keep it (inverse of filterS).
  fn reject(p: A -> Bool, s: Signal(A)) -> Signal(A) =
    match s
      Sig(Some(v)) ->
        pickup
          p(v) -> Sig(None())
          else -> Sig(Some(v))
      Sig(None()) -> Sig(None())

  ## Left-biased merge: emit `sa` if present, otherwise `sb`.
  fn merge(sa: Signal(A), sb: Signal(A)) -> Signal(A) =
    match sa
      Sig(Some(v)) -> Sig(Some(v))
      Sig(None()) -> sb
```

- [ ] **Step 4: Run to verify pass**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: PASS (10 tests).

- [ ] **Step 5: Commit**

```bash
git add lib/std/signal.cure test/cure/stdlib/cure_std_signal_test.exs
git commit -m "feat(std-signal): filterS, reject, merge"
```

---

### Task 4: `foldp` — the stateful primitive (pins the curried-HOF convention, R1)

**Files:**
- Modify: `lib/std/signal.cure`
- Modify: `test/cure/stdlib/cure_std_signal_test.exs`

**Interfaces:**
- Consumes: `Signal(A)` (Task 1).
- Produces: `foldp/3` with signature `(f: A -> S -> S, st: S, sig: Signal(A)) -> Tuple`, runtime shape `%[Signal(S), S]`. The folder `f` is **curried**: applied `f(v)(st)`; tests pass `fn v -> fn s -> ... end end`.

- [ ] **Step 1: Write the failing tests** — append:

```elixir
  describe "foldp" do
    # f is curried: f(val)(state). Build a running-sum folder.
    @sum fn v -> fn s -> v + s end end

    test "present tick folds and emits the new state" do
      assert @sig.foldp(@sum, 10, {:sig, {:some, 5}}) == {{:sig, {:some, 15}}, 15}
    end

    test "absent tick is a no-op: emits absent, state unchanged" do
      assert @sig.foldp(@sum, 10, {:sig, {:none}}) == {{:sig, {:none}}, 10}
    end

    test "state hands off correctly across two consecutive present ticks" do
      {_sig1, st1} = @sig.foldp(@sum, 0, {:sig, {:some, 3}})
      assert {{:sig, {:some, 7}}, 7} = @sig.foldp(@sum, st1, {:sig, {:some, 4}})
    end
  end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: FAIL — `foldp` undefined.

- [ ] **Step 3: Implement** — append to `lib/std/signal.cure`:

```cure
  ## Fold over the past. On a present value, compute `st2 = f(v)(st)` and
  ## emit it; on absent, emit absent and keep `st`. `f` is curried.
  fn foldp(f: A -> S -> S, st: S, sig: Signal(A)) -> Tuple =
    match sig
      Sig(Some(v)) ->
        let st2 = f(v)(st)
        %[Sig(Some(st2)), st2]
      Sig(None()) -> %[Sig(None()), st]
```

- [ ] **Step 4: Run to verify pass**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: PASS (13 tests). If the `@sum` folder errors as not-a-function, the curry convention differs — fix the test's folder shape ONCE here (it is the convention-pinning task) and keep all later stateful-HOF tests consistent with whatever shape passes.

- [ ] **Step 5: Commit**

```bash
git add lib/std/signal.cure test/cure/stdlib/cure_std_signal_test.exs
git commit -m "feat(std-signal): foldp (curried folder, state-in/out)"
```

---

### Task 5: Stateful helpers (`dropRepeats`, `latch`, `count`)

**Files:**
- Modify: `lib/std/signal.cure`
- Modify: `test/cure/stdlib/cure_std_signal_test.exs`

**Interfaces:**
- Consumes: `Signal(A)` (Task 1).
- Produces: `dropRepeats/2` `(prev: Option(A), sig)`, `latch/2` `(prev: A, sig)`, `count/2` `(n: Int, sig)`; each returns `%[output_signal, new_state]`.

- [ ] **Step 1: Write the failing tests** — append:

```elixir
  describe "dropRepeats / latch / count" do
    test "dropRepeats passes the first value and remembers it" do
      assert @sig.dropRepeats({:none}, {:sig, {:some, 7}}) == {{:sig, {:some, 7}}, {:some, 7}}
    end

    test "dropRepeats suppresses a value equal to the previous, state unchanged" do
      assert @sig.dropRepeats({:some, 7}, {:sig, {:some, 7}}) == {{:sig, {:none}}, {:some, 7}}
    end

    test "dropRepeats passes a value different from the previous" do
      assert @sig.dropRepeats({:some, 7}, {:sig, {:some, 8}}) == {{:sig, {:some, 8}}, {:some, 8}}
    end

    test "dropRepeats absent tick keeps prev unchanged" do
      assert @sig.dropRepeats({:some, 7}, {:sig, {:none}}) == {{:sig, {:none}}, {:some, 7}}
    end

    test "latch emits and remembers a present value" do
      assert @sig.latch(0, {:sig, {:some, 9}}) == {{:sig, {:some, 9}}, 9}
    end

    test "latch re-emits the remembered value on an absent tick" do
      assert @sig.latch(9, {:sig, {:none}}) == {{:sig, {:some, 9}}, 9}
    end

    test "count increments only on present ticks" do
      assert @sig.count(2, {:sig, {:some, :anything}}) == {{:sig, {:some, 3}}, 3}
      assert @sig.count(2, {:sig, {:none}}) == {{:sig, {:none}}, 2}
    end
  end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: FAIL — `dropRepeats`/`latch`/`count` undefined.

- [ ] **Step 3: Implement** — append to `lib/std/signal.cure`:

```cure
  ## Suppress a value equal to the previously emitted one. State is the
  ## last emitted value as `Option(A)` (`None()` until the first emit).
  fn dropRepeats(prev: Option(A), sig: Signal(A)) -> Tuple =
    match sig
      Sig(None()) -> %[Sig(None()), prev]
      Sig(Some(v)) ->
        match prev
          Some(p) ->
            pickup
              v == p -> %[Sig(None()), prev]
              else -> %[Sig(Some(v)), Some(v)]
          None() -> %[Sig(Some(v)), Some(v)]

  ## Emit the incoming value when present (and remember it); on absent,
  ## re-emit the last remembered value.
  fn latch(prev: A, sig: Signal(A)) -> Tuple =
    match sig
      Sig(Some(v)) -> %[Sig(Some(v)), v]
      Sig(None()) -> %[Sig(Some(prev)), prev]

  ## Running count of present ticks.
  fn count(n: Int, sig: Signal(A)) -> Tuple =
    match sig
      Sig(Some(_)) ->
        let n2 = n + 1
        %[Sig(Some(n2)), n2]
      Sig(None()) -> %[Sig(None()), n]
```

- [ ] **Step 4: Run to verify pass**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: PASS (20 tests).

- [ ] **Step 5: Commit**

```bash
git add lib/std/signal.cure test/cure/stdlib/cure_std_signal_test.exs
git commit -m "feat(std-signal): dropRepeats, latch, count"
```

---

### Task 6: `every` — interval timer (#3)

**Files:**
- Modify: `lib/std/signal.cure`
- Modify: `test/cure/stdlib/cure_std_signal_test.exs`

**Interfaces:**
- Produces: `every/3` `(interval: Int, now: Int, last: Int) -> Tuple`, runtime `%[Signal(Int), Int]`. Emits `Sig(Some(now))` and new state `now` when `now - last >= interval`, else `Sig(None())` with state unchanged.

- [ ] **Step 1: Write the failing tests** — append:

```elixir
  describe "every" do
    test "fires when the interval has elapsed, emitting now and updating state" do
      assert @sig.every(1000, 1000, 0) == {{:sig, {:some, 1000}}, 1000}
    end

    test "does not fire before the interval elapses, state unchanged" do
      assert @sig.every(1000, 1500, 1000) == {{:sig, {:none}}, 1000}
    end

    test "fires exactly at the interval boundary (>=)" do
      assert @sig.every(1000, 2000, 1000) == {{:sig, {:some, 2000}}, 2000}
    end
  end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: FAIL — `every` undefined.

- [ ] **Step 3: Implement** — append to `lib/std/signal.cure`:

```cure
  ## Emit `now` at most once per `interval`-ms window. State is the last
  ## pulse timestamp; caller seeds `last` (e.g. `now - interval`) so the
  ## first eligible tick fires.
  fn every(interval: Int, now: Int, last: Int) -> Tuple =
    pickup
      now - last >= interval -> %[Sig(Some(now)), now]
      else -> %[Sig(None()), last]
```

- [ ] **Step 4: Run to verify pass**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: PASS (23 tests).

- [ ] **Step 5: Commit**

```bash
git add lib/std/signal.cure test/cure/stdlib/cure_std_signal_test.exs
git commit -m "feat(std-signal): every (interval timer)"
```

---

### Task 7: Edge detection (`risingEdge`, `fallingEdge`) (#3)

**Files:**
- Modify: `lib/std/signal.cure`
- Modify: `test/cure/stdlib/cure_std_signal_test.exs`

**Interfaces:**
- Consumes: `Signal(Bool)`.
- Produces: `risingEdge/2` `(prev: Bool, sig: Signal(Bool)) -> Tuple`, `fallingEdge/2`. Output signal carries unit (`nil`) on an edge; state is the latest observed level.

- [ ] **Step 1: Write the failing tests** — append:

```elixir
  describe "risingEdge / fallingEdge" do
    test "risingEdge fires on false->true, emitting unit, state becomes true" do
      assert @sig.risingEdge(false, {:sig, {:some, true}}) == {{:sig, {:some, nil}}, true}
    end

    test "risingEdge does not fire when level stays true" do
      assert @sig.risingEdge(true, {:sig, {:some, true}}) == {{:sig, {:none}}, true}
    end

    test "risingEdge absent tick keeps prev level" do
      assert @sig.risingEdge(true, {:sig, {:none}}) == {{:sig, {:none}}, true}
    end

    test "fallingEdge fires on true->false, emitting unit, state becomes false" do
      assert @sig.fallingEdge(true, {:sig, {:some, false}}) == {{:sig, {:some, nil}}, false}
    end

    test "fallingEdge does not fire when level stays false" do
      assert @sig.fallingEdge(false, {:sig, {:some, false}}) == {{:sig, {:none}}, false}
    end
  end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: FAIL — `risingEdge`/`fallingEdge` undefined.

- [ ] **Step 3: Implement** — append to `lib/std/signal.cure`:

```cure
  ## Emit unit on a false->true transition of the present level. State is
  ## the latest observed level; absent ticks keep it.
  fn risingEdge(prev: Bool, sig: Signal(Bool)) -> Tuple =
    match sig
      Sig(Some(level)) ->
        pickup
          level == true and prev == false -> %[Sig(Some(nil)), level]
          else -> %[Sig(None()), level]
      Sig(None()) -> %[Sig(None()), prev]

  ## Emit unit on a true->false transition of the present level.
  fn fallingEdge(prev: Bool, sig: Signal(Bool)) -> Tuple =
    match sig
      Sig(Some(level)) ->
        pickup
          level == false and prev == true -> %[Sig(Some(nil)), level]
          else -> %[Sig(None()), level]
      Sig(None()) -> %[Sig(None()), prev]
```

- [ ] **Step 4: Run to verify pass**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: PASS (28 tests).

- [ ] **Step 5: Commit**

```bash
git add lib/std/signal.cure test/cure/stdlib/cure_std_signal_test.exs
git commit -m "feat(std-signal): risingEdge, fallingEdge"
```

---

### Task 8: `debounce` — stable-for-interval filter (#3)

Debounce state is a `%[candidate, since]` tuple — `candidate: Option(A)` (the value being timed) and `since: Int` (when it was first seen). This supersedes the spec's tentative `Debounce(A)` record (the spec explicitly deferred its fields to this plan); a tuple keeps the module record-free and consistent with the other stateful combinators. Initial state: `%[None(), 0]` → runtime `{{:none}, 0}`.

**Files:**
- Modify: `lib/std/signal.cure`
- Modify: `test/cure/stdlib/cure_std_signal_test.exs`

**Interfaces:**
- Consumes: `Signal(A)`.
- Produces: `debounce/4` `(interval: Int, now: Int, st: Tuple, sig: Signal(A)) -> Tuple`, runtime `%[Signal(A), %[Option(A), Int]]`. Emits the value only once it has been the candidate continuously for ≥ `interval` ms.

- [ ] **Step 1: Write the failing tests** — append:

```elixir
  describe "debounce" do
    @init {{:none}, 0}

    test "first appearance starts timing, emits absent, records candidate+since" do
      assert @sig.debounce(50, 100, @init, {:sig, {:some, 7}}) ==
               {{:sig, {:none}}, {{:some, 7}, 100}}
    end

    test "same value before interval elapses stays absent, since unchanged" do
      st = {{:some, 7}, 100}
      assert @sig.debounce(50, 130, st, {:sig, {:some, 7}}) == {{:sig, {:none}}, st}
    end

    test "same value after interval elapses emits the value" do
      st = {{:some, 7}, 100}
      assert @sig.debounce(50, 160, st, {:sig, {:some, 7}}) ==
               {{:sig, {:some, 7}}, {{:some, 7}, 160}}
    end

    test "a different value restarts timing from now" do
      st = {{:some, 7}, 100}
      assert @sig.debounce(50, 120, st, {:sig, {:some, 9}}) ==
               {{:sig, {:none}}, {{:some, 9}, 120}}
    end

    test "absent tick is a no-op: emits absent, state unchanged" do
      st = {{:some, 7}, 100}
      assert @sig.debounce(50, 200, st, {:sig, {:none}}) == {{:sig, {:none}}, st}
    end
  end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: FAIL — `debounce` undefined.

- [ ] **Step 3: Implement** — append to `lib/std/signal.cure`:

```cure
  ## Emit a value only after it has been stable (unchanged) for at least
  ## `interval` ms. State is `%[candidate, since]`: the value being timed
  ## and when it was first seen. Seed with `%[None(), 0]`.
  fn debounce(interval: Int, now: Int, st: Tuple, sig: Signal(A)) -> Tuple =
    match sig
      Sig(None()) -> %[Sig(None()), st]
      Sig(Some(v)) ->
        let %[cand, since] = st
        match cand
          Some(c) ->
            pickup
              c == v and now - since >= interval -> %[Sig(Some(v)), %[Some(v), now]]
              c == v -> %[Sig(None()), st]
              else -> %[Sig(None()), %[Some(v), now]]
          None() -> %[Sig(None()), %[Some(v), now]]
```

- [ ] **Step 4: Run to verify pass**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: PASS (33 tests).

- [ ] **Step 5: Commit**

```bash
git add lib/std/signal.cure test/cure/stdlib/cure_std_signal_test.exs
git commit -m "feat(std-signal): debounce (stable-for-interval)"
```

---

### Task 9: Worked integration demo (pipeline → FSM consumer)

Demonstrates the canonical integration (spec §1, §6): a per-tick pipeline
`debounce → dropRepeats → foldp` threading state across ticks, feeding a tiny
two-mode FSM (the "consumer where real modes exist"). Verified by `cure run`,
which executes the compiled Cure on the host BEAM (same bytecode/semantics as
AtomVM). The demo starts the Cure FSM runtime explicitly via `@extern` — the
documented portability pattern from `esp32-beam/phase3/driver.cure` — so it runs
identically on host BEAM and (later, via the esp32-beam packbeam path) on
generic-unix AtomVM.

**Files:**
- Create: `examples/signal_sensor.cure`

**Interfaces:**
- Consumes: `Cure.Std.Signal.{debounce,dropRepeats,foldp}` (Tasks 8, 5, 4), `Std.Fsm`.

- [ ] **Step 1: Write the failing check**

There is no ExUnit harness for examples; the executable check is a `cure run`
that must print a known line. Define the expected output now: the demo prints
exactly one line `SIGNAL demo: alarms=N final=M` where `N` and `M` are computed
below. First, confirm the failing state:

Run: `cd <worktree> && ./cure run examples/signal_sensor.cure`
Expected: FAIL — file does not exist (`no such file`).

- [ ] **Step 2: Write the demo**

Create `examples/signal_sensor.cure`. The driver feeds a fixed list of
`%[reading, now]` ticks through the full spec pipeline
`debounce -> dropRepeats -> foldp` (simulating one process consuming its mailbox
one message at a time), threads each stage's state, drives an `Alarm` FSM when a
debounced+de-duplicated reading crosses a threshold, and prints a summary
(`foldp` maintains the running alarm count). State threading is explicit
(spec §2).

```cure
fsm Alarm with Integer
  Normal --trip--> Alert
  Alert  --clear--> Normal
  Normal --clear--> Normal
  Alert  --trip--> Alert
  on_transition
    (:normal, :trip,  _p, d) -> %[:ok, :alert,  d + 1]
    (:alert,  :clear, _p, d) -> %[:ok, :normal, d]
    (_, _, _p, d) -> %[:ok, :__same__, d]

mod SignalSensor
  @extern(:io, :put_chars, 1)
  fn puts(s: String) -> Atom

  @extern(:erlang, :atom_to_binary, 1)
  fn atom_to_string(a: Atom) -> String

  @extern(:erlang, :integer_to_binary, 1)
  fn int_to_string(n: Int) -> String

  # Build the runtime FSM module atom from its source name. An `fsm Alarm`
  # container compiles to the module `Cure.FSM.Alarm` (proven in
  # `esp32-beam/phase3/driver.cure`, which builds `Cure.FSM.Turnstile` the
  # same way); a bare `:Alarm` atom would not resolve.
  @extern(:erlang, :binary_to_atom, 1)
  fn to_module(s: String) -> Atom

  # Start Cure's FSM runtime before spawning any FSM (portability pattern:
  # no OTP application boots it under AtomVM; harmless on host BEAM).
  @extern(Elixir.Cure.FSM.Runtime, :start_link, 0)
  fn start_fsm_runtime() -> Any

  # Threshold above which a clean reading trips the alarm.
  fn threshold() -> Int = 50

  # Process one tick: run the value through the full spec pipeline
  # debounce -> dropRepeats -> foldp, and when a clean value emerges, send the
  # Alarm FSM :trip (>= threshold) or :clear. `foldp` folds the clean stream
  # into a running alarm count (its curried folder bumps on a threshold
  # crossing); on an absent tick foldp keeps the count unchanged (absent-tick
  # convention), so there is no double-counting. Carries
  # %[dbState, drState, alarms, pid] and returns the same shape.
  fn step(reading: Int, now: Int, st: Tuple) -> Tuple =
    let %[dbState, drState, alarms, pid] = st
    let %[dbSig, dbState2] = Std.Signal.debounce(30, now, dbState, Std.Signal.constant(reading))
    let %[drSig, drState2] = Std.Signal.dropRepeats(drState, dbSig)
    let bump = fn(v) -> fn(c) ->
      pickup
        v >= threshold() -> c + 1
        else -> c
    let %[_cnt_sig, alarms2] = Std.Signal.foldp(bump, alarms, drSig)
    match drSig
      Sig(Some(v)) ->
        let _e =
          pickup
            v >= threshold() -> send_trip(pid, v)
            else -> send_clear(pid)
        %[dbState2, drState2, alarms2, pid]
      Sig(None()) -> %[dbState2, drState2, alarms2, pid]

  # Helpers so `step` stays readable. Each forwards an event to the FSM.
  fn send_trip(pid: Any, _v: Int) -> Any = Std.Fsm.send(pid, :trip)
  fn send_clear(pid: Any) -> Any = Std.Fsm.send(pid, :clear)

  # Fold the fixed tick list through `step`.
  fn run_ticks(ticks: List(Tuple), st: Tuple) -> Tuple =
    match ticks
      [] -> st
      [%[r, t] | rest] -> run_ticks(rest, step(r, t, st))

  fn start() -> Atom =
    let _r = start_fsm_runtime()
    let pid = Std.Fsm.spawn_with_payload(to_module("Cure.FSM.Alarm"), 0)
    # Same value 60 repeated (debounce passes one, dropRepeats keeps one trip),
    # then a sub-threshold 10 that clears, timestamps 30ms apart so debounce fires.
    let ticks = [%[60, 0], %[60, 40], %[60, 80], %[10, 120], %[10, 160]]
    let initSt = %[%[None(), 0], None(), 0, pid]
    let finalSt = run_ticks(ticks, initSt)
    let %[_db, _dr, alarms, _pid] = finalSt
    let finalState = Std.Fsm.state(pid)
    let _p = puts("SIGNAL demo: alarms=" <> int_to_string(alarms) <> " final=" <> atom_to_string(finalState) <> "\n")
    :ok
```

> **Traced expectation:** with these five ticks and `threshold = 50`, debounce
> (30ms window) admits the first stable `60` at tick 2, `dropRepeats` emits it
> once (tick 3's repeat is suppressed), `foldp` bumps the count to `1`, and the
> FSM trips `Normal -> Alert`; tick 5's stable `10` is a new value, emitted by
> `dropRepeats`, below threshold, so `foldp` keeps the count at `1` and the FSM
> clears `Alert -> Normal`. Output line: `SIGNAL demo: alarms=1 final=normal`.
> The exact numbers are observational; the gating requirement is the printed
> line in this format with the pipeline intact.

> **Implementer note (two bounded risks — resolve, do not weaken the pipeline):**
> 1. **`Std.Fsm` API:** `send`/`spawn_with_payload`/`state` and the
>    `to_module("Cure.FSM.Alarm")` spawn key are used exactly as in
>    `esp32-beam/phase3/driver.cure` (which spawns `to_module("Cure.FSM.Turnstile")`).
>    Verify against `lib/std/fsm.cure` + `driver.cure`; if the spawn key or
>    `state` accessor differs, adjust so the program prints one
>    `SIGNAL demo: alarms=<int> final=<atom>` line. (`Std.Fsm.state/1` returns the
>    state Atom — proven in driver.cure.)
> 2. **Matching the `Sig` constructor in `step`:** `Sig`/`Signal` are defined in
>    `Std.Signal`. If Cure rejects the bare `Sig(Some(v))` pattern from another
>    module (unresolved constructor), first try qualifying it
>    (`Std.Signal.Sig(...)`); if cross-module constructor patterns are not
>    supported, add a minimal eliminator to `Std.Signal` — `fn withDefault(default:
>    A, s: Signal(A)) -> A` (present-value-or-default), with its own red/green
>    test in `cure_std_signal_test.exs` — and rewrite `step` to use
>    `Std.Signal.withDefault(-1, drSig)` then branch on the sentinel `-1`. This is
>    the one sanctioned API addition (an eliminator the spec's transformer-only
>    §4 lacks); keep the debounce → dropRepeats pipeline intact either way.
>
> The *gating requirement* is a clean compile + a single printed
> `SIGNAL demo: alarms=<int> final=<atom>` line with the pipeline intact; exact
> count/state values are observational.

- [ ] **Step 3: Run to verify it compiles and runs**

Run: `cd <worktree> && ./cure run examples/signal_sensor.cure`
Expected: a single line beginning `SIGNAL demo:`. If `cure run` cannot resolve
`Std.Signal`/`Std.Fsm` for an example, compile the stdlib first
(`mix cure.compile_stdlib`) and rerun; if the FSM runtime fails to start on the
host, the explicit `start_fsm_runtime()` call is already present — surface any
remaining runtime error as a Stage-4 blocker rather than removing the FSM.

- [ ] **Step 4: Confirm the combinators are exercised**

Verify the printed line appears and the program exits 0. This is the closing
on-VM evidence that `Std.Signal` composes in a real program.

- [ ] **Step 5: Commit**

```bash
git add examples/signal_sensor.cure
git commit -m "feat(std-signal): worked sensor pipeline + FSM demo"
```

---

## Self-Review

**1. Spec coverage:**
- §4a stateless (`constant`, `never`, `map`, `filterS`, `reject`, `merge`, `mapTo`, `toUnit`) → Tasks 1–3. ✓
- §4b stateful (`foldp`, `dropRepeats`, `latch`, `count`) → Tasks 4–5. ✓
- §4c timer/edge (`every`, `risingEdge`, `fallingEdge`, `debounce`) → Tasks 6–8. ✓
- §6 ExUnit harness + runtime encoding → Task 1 establishes it; every task asserts in the verified encoding. ✓
- §1/§6 worked demo (pipeline → FSM, on-VM) → Task 9. ✓
- Absent-tick convention → tested in Tasks 4, 5, 7, 8. ✓
- v2 / out-of-scope items (`zip`, `Pipeline`, capacity types, hardware flashing) → correctly absent. ✓

**2. Placeholder scan:** No "TBD"/"handle edge cases"/"similar to Task N". Every code step shows complete code. The one deferral the spec sanctioned (`debounce` state fields) is resolved concretely in Task 8 (a `%[candidate, since]` tuple). ✓

**3. Type consistency:** `Signal(A) = Sig(Option(A))` defined in Task 1 and matched as `Sig(Some(_))`/`Sig(None())` everywhere. Stateful returns are uniformly `%[output_signal, new_state]` → `{output, state}` at runtime. The curried-folder convention (`f(v)(st)`) is pinned in Task 4 and reused once more in the Task 9 demo's `foldp` alarm counter (anonymous curried `fn(v) -> fn(c) -> ...`, the shape proven in `lib/std/list.cure`); other stateful combinators take no folder. `debounce` state shape `{{candidate}, since}` is consistent between its implementation and its tests. Demo (Task 9) consumes `debounce`/`dropRepeats`/`foldp` with the exact arities defined in Tasks 8/5/4. ✓

**Two spec-sanctioned refinements, made explicit:** (1) folder type curried `A -> S -> S` (spec R1 said to pin the calling convention here; forced by Cure); (2) `debounce` state is a tuple, not the tentative `Debounce(A)` record (spec deferred the fields to this plan). Neither changes any combinator's parameter set, types, or semantics.
