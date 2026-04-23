# TODO: Future Cure example projects

Parked showcase projects -- the two candidates generated alongside
`cure_motif` that we did not pick for immediate implementation. Both
are self-contained, mid-sized (~500-800 LOC of `.cure` + harness),
and exercise Cure features that no existing `examples/*` project
puts at the centre.

When one of these is promoted, add a fresh entry to `stuff/plans/`
with a file-by-file breakdown before writing code.

---

## 1. `cure_tempus` -- verified cron scheduler

### Pitch

A miniature Quartz/cron that is provably safe: no job fires twice in
the same tick, every `Scheduled` job reaches a terminal state within
its deadline, and every `Cron` literal is validated by Z3 at compile
time.

### Feature coverage

- **Refinement types + SMT.** `type Minute = {m: Int | m >= 0 and m <= 59}`
  and the rest of the cron fields. A cron literal such as
  `Cron{minute: 61, ...}` is rejected by `cure check`, not at
  runtime.
- **`Std.Regex`** parses `"*/5 9-17 * * MON-FRI"` strings into the
  refined record, with compile-time error messages routed through
  `Cure.Compiler.Errors`.
- **FSM per job**, callback mode:
  `Idle -> Scheduled -> Running -> (Succeeded | Failed | Cancelled)`,
  with `schedule!`, `fire!`, `complete?`, `fail?`, `cancel!`, an
  `on_timer` lifecycle, and an `on_failure` rollback.
- **`Cure.Temporal`** LTL properties:
  `always (Running -> eventually (Succeeded or Failed))` and
  `never (Running and Running')` (no double-fire in the same tick).
- **Typed actors + supervisor**: `actor Scheduler`, `actor JobWorker`,
  `sup Tempus.Root` wiring them as `:one_for_one`. Timed sends via
  the Melquiades Operator.
- **OTP `app` + `cure release`** with `Cure.toml [application]` and
  `[release]` sections, shipping as a bootable BEAM release.
- **Observability**: `cure top` shows live queue depth and FSM state
  distribution; `cure trace` follows a single `JobId`.
- **`Std.Time`** for monotonic tick scheduling; **`Std.Json`** for
  dumping run history.

### Why it is persuasive

It is a product category everyone has used (Quartz, cron, Sidekiq,
Oban), so reviewers can instantly map Cure's guarantees onto pain
they already know.

### Rough scope

~500-700 LOC of `.cure` plus tests, in a single project directory
under `examples/cure_tempus/`.

---

## 2. `cure_rendezvous` -- session-typed circuit breaker with a CRDT token bucket

### Pitch

A network-facing rate-limiter + circuit-breaker library whose
client/server handshake is described as a `Cure.Protocol` session
type, whose token bucket is a `Std.CRDT` PN-counter replicated across
nodes, and whose breaker is an FSM whose recovery liveness is proved
with `Cure.Temporal`.

### Feature coverage

- **Session types (`Cure.Protocol`).** The public surface is
  `!Acquire(amount) -> ?Granted | ?Retry(after_ms) | ?Tripped`. The
  Cure checker refuses code that sends `Release` before `Acquire`
  was granted.
- **Refinement types.** `amount: {n: Nat | n > 0 and n <= capacity}`,
  `capacity: {c: Nat | c > 0}`. Token count invariant
  `tokens >= 0 and tokens <= capacity` is threaded through every
  transition.
- **CRDTs** (`Std.CRDT`). Token bucket is a PN-counter; converges
  across nodes without a coordinator. Great showcase of `Std.CRDT`
  as a first-class stdlib feature.
- **FSM**, callback mode:
  `Closed -> Open -> HalfOpen -> (Closed | Open)`, with `trip!`,
  `probe?`, `reset!`, `on_timer` for the half-open probe window,
  `on_enter` for metric emission.
- **`Cure.Temporal`.** Two specs:
  `always (Open -> eventually_within k HalfOpen)` (recovery
  liveness) and `never (Tripped and not_admitted_in_last_window)`
  (no silent drops).
- **Typed actors + supervisor.** `actor Breaker`, `actor Bucket`,
  `sup Rendezvous.Root`. Melquiades Operator for the typed sends
  across the breaker boundary.
- **`@record` + `cure replay`.** Journal a live failure cascade;
  replay it deterministically in the REPL to demonstrate
  time-travel debugging.
- **OpenTelemetry**: emit `Cure.OTel` spans around every
  `acquire`/`release`; shown from `cure top` and `cure trace`.

### Why it is persuasive

Rate-limiters + breakers are the canonical "operationally scary"
primitive. Showing them end-to-end verified is exactly what
dependently-typed OTP is for.

### Rough scope

~600-800 LOC, probably two Cure modules plus a small Elixir
driver/test harness, under `examples/cure_rendezvous/`.
