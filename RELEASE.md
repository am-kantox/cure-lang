# Cure v0.16.0 -- Finitomata-Inspired FSM Rewrite

Cure is a dependently-typed programming language for the BEAM virtual machine
with first-class finite state machines and SMT-backed verification.

v0.16.0 completely rethinks FSM handling. Inspired by
[Finitomata](https://hexdocs.pm/finitomata), FSM definitions and transition
logic now coexist in the same `.cure` file. The new callback mode compiles
to `GenServer`-based modules with inline `on_transition` handlers, while
simple mode (backward-compatible `gen_statem`) gains introspection APIs and
event suffix support.

## Highlights

### Dual-Mode FSM Compilation
- **Callback mode** (new): `on_transition` block compiles to a `GenServer`
  with embedded transition table and user-defined dispatch clauses
- **Simple mode** (enhanced): `gen_statem` now exports `transitions/0`,
  `allowed/2`, and supports hard/soft event suffixes

### Event Suffixes
- `event!` -- hard/determined: auto-fires when the FSM enters a state where
  this is the sole outgoing event
- `event?` -- soft: failed transitions are silently swallowed

### Lifecycle Callbacks
- `on_enter`, `on_exit`, `on_failure`, `on_timer`

### Introspection API
- `transitions/0`, `allowed/2` / `allowed?/2`, `responds?/2`

### Compile-Time Verification
- Hard event validation, ambiguous transition warnings, coverage analysis
- All existing checks preserved (reachability, deadlock freedom, terminal states)

### Tooling
- LSP: FSM transitions as document symbols; hover for callbacks; completions
- MCP: enhanced `analyze_fsm`; rewritten FSM syntax help

## Example

```cure
fsm Turnstile with Integer
  Locked   --coin-->  Unlocked
  Unlocked --push-->  Locked
  Unlocked --coin-->  Unlocked
  Locked   --push-->  Locked

  on_transition
    (:locked, :coin, _payload, data) -> %[:ok, :unlocked, data + 1]
    (:unlocked, :push, _payload, data) -> %[:ok, :locked, data]
    (_, _, _, data) -> %[:ok, :__same__, data]
```

## Changes since v0.15.0

See CHANGELOG.md for the full list.

## The numbers

714 tests (all passing). Zero compilation warnings. Zero credo issues.
55 Elixir source files. 18 stdlib modules.
