# Std.Signal v2 Combinators Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add 13 v2 combinators to the existing `Std.Signal` module, each verified by an ExUnit test, with no regressions to v1's 35 tests.

**Architecture:** Append pure-Cure functions to `lib/std/signal.cure` (already holds v1's `Signal(A) = Sig(Option(A))` + 17 combinators) and append ExUnit assertions to `test/cure/stdlib/cure_std_signal_test.exs`. Same TDD harness as v1: `mix test` recompiles the stdlib before running. No FFI, no new example program.

**Tech Stack:** Cure, Elixir/ExUnit, `mix`.

**Source spec:** `docs/superpowers/specs/2026-06-27-signal-combinators-v2-design.md` (hardened). Read §4 (combinators) and §3 (research finding) first.

## Global Constraints

Copied from the spec + verified v1 codebase conventions; apply to EVERY task:

- **Append only.** Add functions after v1's last function in `lib/std/signal.cure`; do NOT modify v1 functions or their tests (v1 tests are immutable and must stay green).
- **snake_case names** (Cure downcases function names at the BEAM boundary; v1 lesson).
- **`Signal(A) = Sig(Option(A))`** already defined (v1). Match as `Sig(Some(v))` / `Sig(None())`. Nullary constructors built/matched with `()`.
- **Stateful combinators return the built-in `Tuple`** (`-> Tuple`); the `%[output, state]` form is the runtime tuple shape.
- **Curried HOF params at arity ≥2**: `map2`'s `f: A -> B -> C` is applied `f(a)(b)`; tests pass `fn a -> fn b -> ... end end`. Arity-1 HOF params (`filter_map`, `partition`, `sample` predicates/funcs) are plain `fn x -> ... end`.
- **Runtime encodings (ExUnit), verified in v1:** `Some(x)`→`{:some, x}`; `None()`→`{:none}`; `Sig(Some(5))`→`{:sig, {:some, 5}}`; `Sig(None())`→`{:sig, {:none}}`; Cure tuple `%[a, b]`→`{a, b}`; `Unit nil`→`nil`. So a `%[Signal, state]` return is `{ {:sig, ...}, state }`; nested `Sig(Some(%[1,2]))`→`{:sig, {:some, {1, 2}}}`; `Sig(Some(Some(7)))`→`{:sig, {:some, {:some, 7}}}`.
- **Integer division:** `/` on `Int` operands yields a truncated `Int` (verified: `lib/std/math.cure` `safe_div`). `running_mean` only divides when count ≥ 1.
- **Private helpers** use `local fn` (verified in `lib/std/access.cure`).
- **Cure forms confirmed safe** (use these; avoid `or`, `let x = match`, `let x = pickup` — no stdlib precedent): `match`/arms, `pickup`/`else` (as a match-arm body or function body), `and`, `==`, `+`, `-`, `/`, `let %[a,b] = t` destructuring, single-line curried lambda `fn(a) -> fn(b) -> expr`, multi-statement match arms with `let`.
- **TDD per task:** append failing tests → `mix test test/cure/stdlib/cure_std_signal_test.exs` (red) → implement → rerun (green) → commit. One `mix test` at a time.
- **All git ops inside the worktree** (`/Users/ch/Develop/esp32-beam/cure-lang/.claude/worktrees/std-signal`) so commits land on `autopilot/std-signal`.

**Test-file append anchor:** new `describe` blocks go immediately before the final `end` of the `Cure.Stdlib.SignalTest` module (after v1's `with_default` describe). New `defp` test helpers go beside the existing `defp sum_folder` (top level of the module).

**Signal-file append anchor:** new functions go after v1's last function (`with_default`).

---

### Task 1: `merge_all` + `filter_map` (stateless)

**Files:**
- Modify: `lib/std/signal.cure`
- Modify: `test/cure/stdlib/cure_std_signal_test.exs`

**Interfaces:**
- Consumes: `Signal(A)`, `Option` (v1/Core).
- Produces: `merge_all/1` `(List(Signal(A))) -> Signal(A)`; `filter_map/2` `(f: A -> Option(B), s) -> Signal(B)`.

- [ ] **Step 1: Append failing tests** (before the module's final `end`):

```elixir
  describe "merge_all / filter_map" do
    test "merge_all returns the first present signal, left-biased" do
      assert @sig.merge_all([{:sig, {:none}}, {:sig, {:some, 2}}, {:sig, {:some, 3}}]) ==
               {:sig, {:some, 2}}
    end

    test "merge_all of all-absent (and of empty) is absent" do
      assert @sig.merge_all([{:sig, {:none}}, {:sig, {:none}}]) == {:sig, {:none}}
      assert @sig.merge_all([]) == {:sig, {:none}}
    end

    test "filter_map keeps mapped Some, drops mapped None and absence" do
      keep_even = fn x -> if rem(x, 2) == 0, do: {:some, x * 10}, else: {:none} end
      assert @sig.filter_map(keep_even, {:sig, {:some, 4}}) == {:sig, {:some, 40}}
      assert @sig.filter_map(keep_even, {:sig, {:some, 3}}) == {:sig, {:none}}
      assert @sig.filter_map(keep_even, {:sig, {:none}}) == {:sig, {:none}}
    end
  end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: FAIL — `merge_all`/`filter_map` undefined.

- [ ] **Step 3: Implement** — append to `lib/std/signal.cure`:

```cure
  ## Left-biased N-ary merge: the first present signal in the list, else
  ## absent. Empty list is absent.
  fn merge_all(sigs: List(Signal(A))) -> Signal(A) =
    match sigs
      [] -> Sig(None())
      [s | rest] ->
        match s
          Sig(Some(v)) -> Sig(Some(v))
          Sig(None()) -> merge_all(rest)

  ## Map and keep only the `Some` results: present `v` whose `f(v)` is
  ## `Some(b)` emits `b`; `None()` (and an absent input) emit absent.
  fn filter_map(f: A -> Option(B), s: Signal(A)) -> Signal(B) =
    match s
      Sig(Some(v)) ->
        match f(v)
          Some(b) -> Sig(Some(b))
          None() -> Sig(None())
      Sig(None()) -> Sig(None())
```

- [ ] **Step 4: Run to verify pass**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: PASS (all green, including the 3 new tests).

- [ ] **Step 5: Commit**

```bash
git add lib/std/signal.cure test/cure/stdlib/cure_std_signal_test.exs
git commit -m "feat(std-signal): merge_all, filter_map"
```

---

### Task 2: `map2` + `zip` (combine two streams)

**Files:**
- Modify: `lib/std/signal.cure`
- Modify: `test/cure/stdlib/cure_std_signal_test.exs`

**Interfaces:**
- Consumes: `Signal(A)`.
- Produces: `map2/4` `(f: A -> B -> C, st: Tuple, sa, sb) -> Tuple` (runtime `%[Signal(C), %[lastA, lastB]]`); `zip/3` `(st: Tuple, sa, sb) -> Tuple` (runtime `%[Signal(Tuple), %[lastA, lastB]]`). Two private helpers `sig_or/2`, `either_present/2`.

- [ ] **Step 1: Append the curried test helper** beside `defp sum_folder` (top of the test module):

```elixir
  # f for map2 is curried: f(a)(b). Running-add combiner.
  defp add2, do: fn a -> fn b -> a + b end end
```

- [ ] **Step 2: Append failing tests** (before the module's final `end`):

```elixir
  describe "map2 / zip" do
    test "map2 fires when either input is present, using the latest of the other" do
      # state seeds lastA=0, lastB=0; a=3 arrives, b absent -> 3 + last b(0)
      assert @sig.map2(add2(), {0, 0}, {:sig, {:some, 3}}, {:sig, {:none}}) ==
               {{:sig, {:some, 3}}, {3, 0}}
      # next tick: b=4 arrives, a absent -> remembered a(3) + 4
      assert @sig.map2(add2(), {3, 0}, {:sig, {:none}}, {:sig, {:some, 4}}) ==
               {{:sig, {:some, 7}}, {3, 4}}
    end

    test "map2 with neither present emits absent, state unchanged" do
      assert @sig.map2(add2(), {3, 4}, {:sig, {:none}}, {:sig, {:none}}) ==
               {{:sig, {:none}}, {3, 4}}
    end

    test "zip pairs the latest values when either fires" do
      assert @sig.zip({0, 0}, {:sig, {:some, 1}}, {:sig, {:some, 2}}) ==
               {{:sig, {:some, {1, 2}}}, {1, 2}}
    end
  end
```

- [ ] **Step 3: Run to verify failure**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: FAIL — `map2`/`zip` undefined.

- [ ] **Step 4: Implement** — append to `lib/std/signal.cure`:

```cure
  ## Present value, or the supplied default when absent (internal).
  local fn sig_or(s: Signal(A), default: A) -> A =
    match s
      Sig(Some(v)) -> v
      Sig(None()) -> default

  ## True when at least one of the two signals is present (internal).
  local fn either_present(sa: Signal(A), sb: Signal(B)) -> Bool =
    match sa
      Sig(Some(_)) -> true
      Sig(None()) ->
        match sb
          Sig(Some(_)) -> true
          Sig(None()) -> false

  ## Combine two streams (a.k.a. combine_latest): state `%[lastA, lastB]`.
  ## Each present value updates its slot; emit `f(na)(nb)` if either input
  ## is present this tick, else absent. `f` is curried.
  fn map2(f: A -> B -> C, st: Tuple, sa: Signal(A), sb: Signal(B)) -> Tuple =
    let %[la, lb] = st
    let na = sig_or(sa, la)
    let nb = sig_or(sb, lb)
    match either_present(sa, sb)
      true -> %[Sig(Some(f(na)(nb))), %[na, nb]]
      false -> %[Sig(None()), %[na, nb]]

  ## `map2` specialised to pair the latest values into a tuple signal.
  fn zip(st: Tuple, sa: Signal(A), sb: Signal(B)) -> Tuple =
    let mk = fn(a) -> fn(b) -> %[a, b]
    map2(mk, st, sa, sb)
```

- [ ] **Step 5: Run to verify pass**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: PASS (3 new tests green).

- [ ] **Step 6: Commit**

```bash
git add lib/std/signal.cure test/cure/stdlib/cure_std_signal_test.exs
git commit -m "feat(std-signal): map2, zip (combine two streams)"
```

---

### Task 3: `unzip` + `partition` (split a stream)

**Files:**
- Modify: `lib/std/signal.cure`
- Modify: `test/cure/stdlib/cure_std_signal_test.exs`

**Interfaces:**
- Produces: `unzip/1` `(Signal(Tuple)) -> Tuple` (runtime `%[Signal(A), Signal(B)]`); `partition/2` `(p: A -> Bool, s) -> Tuple` (runtime `%[matching, non_matching]`).

- [ ] **Step 1: Append failing tests** (before the module's final `end`):

```elixir
  describe "unzip / partition" do
    test "unzip splits a present tuple-signal into two present signals" do
      assert @sig.unzip({:sig, {:some, {1, 2}}}) == {{:sig, {:some, 1}}, {:sig, {:some, 2}}}
      assert @sig.unzip({:sig, {:none}}) == {{:sig, {:none}}, {:sig, {:none}}}
    end

    test "partition routes present values by the predicate" do
      big = fn x -> x > 10 end
      assert @sig.partition(big, {:sig, {:some, 20}}) == {{:sig, {:some, 20}}, {:sig, {:none}}}
      assert @sig.partition(big, {:sig, {:some, 5}}) == {{:sig, {:none}}, {:sig, {:some, 5}}}
      assert @sig.partition(big, {:sig, {:none}}) == {{:sig, {:none}}, {:sig, {:none}}}
    end
  end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: FAIL — `unzip`/`partition` undefined.

- [ ] **Step 3: Implement** — append to `lib/std/signal.cure`:

```cure
  ## Split a tuple-signal into two signals. Absent -> both absent.
  fn unzip(s: Signal(Tuple)) -> Tuple =
    match s
      Sig(Some(pair)) ->
        let %[a, b] = pair
        %[Sig(Some(a)), Sig(Some(b))]
      Sig(None()) -> %[Sig(None()), Sig(None())]

  ## Route a present value: `%[matching, non_matching]`. Absent -> both absent.
  fn partition(p: A -> Bool, s: Signal(A)) -> Tuple =
    match s
      Sig(Some(v)) ->
        pickup
          p(v) -> %[Sig(Some(v)), Sig(None())]
          else -> %[Sig(None()), Sig(Some(v))]
      Sig(None()) -> %[Sig(None()), Sig(None())]
```

- [ ] **Step 4: Run to verify pass**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: PASS (2 new tests green).

- [ ] **Step 5: Commit**

```bash
git add lib/std/signal.cure test/cure/stdlib/cure_std_signal_test.exs
git commit -m "feat(std-signal): unzip, partition"
```

---

### Task 4: `throttle` + `sample` (rate-limit + sampling)

**Files:**
- Modify: `lib/std/signal.cure`
- Modify: `test/cure/stdlib/cure_std_signal_test.exs`

**Interfaces:**
- Produces: `throttle/4` `(interval: Int, now: Int, last_emit: Int, s) -> Tuple` (runtime `%[Signal(A), Int]`); `sample/2` `(held: A, trigger: Signal(B)) -> Signal(A)`.

- [ ] **Step 1: Append failing tests** (before the module's final `end`):

```elixir
  describe "throttle / sample" do
    test "throttle emits when the interval has elapsed, then suppresses" do
      assert @sig.throttle(100, 100, 0, {:sig, {:some, :a}}) == {{:sig, {:some, :a}}, 100}
      assert @sig.throttle(100, 150, 100, {:sig, {:some, :b}}) == {{:sig, {:none}}, 100}
      assert @sig.throttle(100, 200, 100, {:sig, {:some, :c}}) == {{:sig, {:some, :c}}, 200}
    end

    test "throttle passes an absent tick through, state unchanged" do
      assert @sig.throttle(100, 999, 100, {:sig, {:none}}) == {{:sig, {:none}}, 100}
    end

    test "sample emits the held value when the trigger fires" do
      assert @sig.sample(42, {:sig, {:some, :tick}}) == {:sig, {:some, 42}}
      assert @sig.sample(42, {:sig, {:none}}) == {:sig, {:none}}
    end
  end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: FAIL — `throttle`/`sample` undefined.

- [ ] **Step 3: Implement** — append to `lib/std/signal.cure`:

```cure
  ## Leading-edge rate-limit: emit a present value if `now - last_emit >=
  ## interval` (new state `now`); otherwise absent, state unchanged. Caller
  ## seeds `last_emit` (e.g. `now - interval`) so the first value fires.
  fn throttle(interval: Int, now: Int, last_emit: Int, s: Signal(A)) -> Tuple =
    match s
      Sig(Some(v)) ->
        pickup
          now - last_emit >= interval -> %[Sig(Some(v)), now]
          else -> %[Sig(None()), last_emit]
      Sig(None()) -> %[Sig(None()), last_emit]

  ## Emit the `held` value whenever `trigger` is present, else absent
  ## (event x behavior sampling; the host threads `held`, e.g. via `latch`).
  fn sample(held: A, trigger: Signal(B)) -> Signal(A) =
    match trigger
      Sig(Some(_)) -> Sig(Some(held))
      Sig(None()) -> Sig(None())
```

- [ ] **Step 4: Run to verify pass**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: PASS (3 new tests green).

- [ ] **Step 5: Commit**

```bash
git add lib/std/signal.cure test/cure/stdlib/cure_std_signal_test.exs
git commit -m "feat(std-signal): throttle, sample"
```

---

### Task 5: `meta` + `unmeta` (reify presence)

**Files:**
- Modify: `lib/std/signal.cure`
- Modify: `test/cure/stdlib/cure_std_signal_test.exs`

**Interfaces:**
- Produces: `meta/1` `(Signal(A)) -> Signal(Option(A))`; `unmeta/1` `(Signal(Option(A))) -> Signal(A)`.

- [ ] **Step 1: Append failing tests** (before the module's final `end`):

```elixir
  describe "meta / unmeta" do
    test "meta reifies presence as an always-present Option signal" do
      assert @sig.meta({:sig, {:some, 7}}) == {:sig, {:some, {:some, 7}}}
      assert @sig.meta({:sig, {:none}}) == {:sig, {:some, {:none}}}
    end

    test "unmeta is the inverse of meta" do
      assert @sig.unmeta({:sig, {:some, {:some, 7}}}) == {:sig, {:some, 7}}
      assert @sig.unmeta({:sig, {:some, {:none}}}) == {:sig, {:none}}
      assert @sig.unmeta({:sig, {:none}}) == {:sig, {:none}}
    end
  end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: FAIL — `meta`/`unmeta` undefined.

- [ ] **Step 3: Implement** — append to `lib/std/signal.cure`:

```cure
  ## Reify presence: an always-present signal carrying the input as an
  ## `Option`. Present `v` -> `Some(Some(v))`; absent -> `Some(None())`.
  fn meta(s: Signal(A)) -> Signal(Option(A)) =
    match s
      Sig(Some(v)) -> Sig(Some(Some(v)))
      Sig(None()) -> Sig(Some(None()))

  ## Inverse of `meta`: collapse a signal of `Option` back to a signal.
  fn unmeta(s: Signal(Option(A))) -> Signal(A) =
    match s
      Sig(Some(Some(v))) -> Sig(Some(v))
      Sig(Some(None())) -> Sig(None())
      Sig(None()) -> Sig(None())
```

- [ ] **Step 4: Run to verify pass**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: PASS (2 new tests green).

- [ ] **Step 5: Commit**

```bash
git add lib/std/signal.cure test/cure/stdlib/cure_std_signal_test.exs
git commit -m "feat(std-signal): meta, unmeta"
```

---

### Task 6: `toggle` + `running_sum` + `running_mean` (stateful accumulators)

**Files:**
- Modify: `lib/std/signal.cure`
- Modify: `test/cure/stdlib/cure_std_signal_test.exs`

**Interfaces:**
- Produces: `toggle/4` `(a: A, b: A, st: A, trigger: Signal(C)) -> Tuple`; `running_sum/2` `(st: Int, s: Signal(Int)) -> Tuple`; `running_mean/2` `(st: Tuple, s: Signal(Int)) -> Tuple` (state `%[sum, count]`).

- [ ] **Step 1: Append failing tests** (before the module's final `end`):

```elixir
  describe "toggle / running_sum / running_mean" do
    test "toggle flips between two values on each present trigger" do
      assert @sig.toggle(:off, :on, :off, {:sig, {:some, :press}}) == {{:sig, {:some, :on}}, :on}
      assert @sig.toggle(:off, :on, :on, {:sig, {:some, :press}}) == {{:sig, {:some, :off}}, :off}
    end

    test "toggle on an absent trigger emits absent, state unchanged" do
      assert @sig.toggle(:off, :on, :on, {:sig, {:none}}) == {{:sig, {:none}}, :on}
    end

    test "running_sum accumulates present values" do
      assert @sig.running_sum(10, {:sig, {:some, 5}}) == {{:sig, {:some, 15}}, 15}
      assert @sig.running_sum(10, {:sig, {:none}}) == {{:sig, {:none}}, 10}
    end

    test "running_mean reports the truncating integer average" do
      assert @sig.running_mean({0, 0}, {:sig, {:some, 10}}) == {{:sig, {:some, 10}}, {10, 1}}
      # {sum 10, count 1} + 5 -> sum 15, count 2, mean 15/2 = 7 (truncated)
      assert @sig.running_mean({10, 1}, {:sig, {:some, 5}}) == {{:sig, {:some, 7}}, {15, 2}}
      assert @sig.running_mean({10, 1}, {:sig, {:none}}) == {{:sig, {:none}}, {10, 1}}
    end
  end
```

- [ ] **Step 2: Run to verify failure**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: FAIL — `toggle`/`running_sum`/`running_mean` undefined.

- [ ] **Step 3: Implement** — append to `lib/std/signal.cure`:

```cure
  ## Flip between `a` and `b` on each present trigger. State is the current
  ## value (seed with `a` or `b`). Absent trigger -> absent, state unchanged.
  fn toggle(a: A, b: A, st: A, trigger: Signal(C)) -> Tuple =
    match trigger
      Sig(Some(_)) ->
        pickup
          st == a -> %[Sig(Some(b)), b]
          else -> %[Sig(Some(a)), a]
      Sig(None()) -> %[Sig(None()), st]

  ## Running total of present `Int` values.
  fn running_sum(st: Int, s: Signal(Int)) -> Tuple =
    match s
      Sig(Some(v)) ->
        let s2 = st + v
        %[Sig(Some(s2)), s2]
      Sig(None()) -> %[Sig(None()), st]

  ## Moving average. State `%[sum, count]`; each present `v` updates both
  ## and emits the truncating integer mean (count >= 1 here, so no div0).
  ## Seed with `%[0, 0]`.
  fn running_mean(st: Tuple, s: Signal(Int)) -> Tuple =
    match s
      Sig(Some(v)) ->
        let %[sum, cnt] = st
        let sum2 = sum + v
        let cnt2 = cnt + 1
        let mean = sum2 / cnt2
        %[Sig(Some(mean)), %[sum2, cnt2]]
      Sig(None()) -> %[Sig(None()), st]
```

- [ ] **Step 4: Run to verify pass**

Run: `mix test test/cure/stdlib/cure_std_signal_test.exs`
Expected: PASS (4 new tests green).

- [ ] **Step 5: Commit**

```bash
git add lib/std/signal.cure test/cure/stdlib/cure_std_signal_test.exs
git commit -m "feat(std-signal): toggle, running_sum, running_mean"
```

---

## Self-Review

**1. Spec coverage:**
- §4a stateless (`merge_all`, `filter_map`, `unzip`, `partition`, `sample`, `meta`, `unmeta`) → Tasks 1, 3, 4, 5. ✓
- §4b stateful (`map2`, `zip`, `throttle`, `toggle`, `running_sum`, `running_mean`) → Tasks 2, 4, 6. ✓ (All 13 combinators covered.)
- §3 research finding → already documented in the spec; no code task (it's a "don't build" finding). ✓
- §6 verification (ExUnit, present/absent/state-handoff per combinator) → each task's tests cover present, absent, and (stateful) two-tick handoff (`map2` two-tick, `throttle` boundary + suppress, `toggle` flip, `running_mean` div). ✓
- §5 purity (no FFI) → every implementation uses only `match`/`pickup`/`+`/`-`/`/`/`==` and `local fn`; no `@extern`. ✓
- §7 out-of-scope (variadic merge, buffer_n, join, delay/distinct/sink) → correctly absent. ✓

**2. Placeholder scan:** No "TBD"/"handle edge cases". Every code step has complete code. ✓

**3. Type consistency:** Stateful returns are uniformly `%[output, state]` → `{output, state}`. `map2`'s curried `f(na)(nb)` matches the `defp add2` shape `fn a -> fn b -> ... end end` and v1's foldp convention. `zip` calls `map2` with the curried `mk = fn(a) -> fn(b) -> %[a,b]`. `running_mean` state shape `{sum, count}` is consistent between impl and tests. `sig_or`/`either_present` are `local fn` (private), used only inside `map2`. No name collides with v1's 17 functions (`constant, never, map, map_to, to_unit, filter_s, reject, merge, foldp, drop_repeats, latch, count, every, rising_edge, falling_edge, debounce, with_default`). ✓
