# CureTurnstile

An example application demonstrating Cure's first-class FSM support.

A classic turnstile state machine is defined in Cure's FSM syntax and compiled
to a BEAM `gen_statem` module. An Elixir `GenServer` wrapper adds coin and
passage counting on top.

## State Machine

```
  +--------+  coin   +----------+
  | Locked |-------->| Unlocked |
  +--------+         +----------+
    ^  |  push(nop)   |  ^  coin(nop)
    |  +-------+       |  +------+
    |          |       |
    +----------+-------+
        push
```

Defined in `cure_src/turnstile.cure`:

```cure
fsm Turnstile with Integer
  Locked   --coin-->  Unlocked
  Unlocked --push-->  Locked
  Unlocked --coin-->  Unlocked
  Locked   --push-->  Locked

  on_transition
    (:locked, :coin, _payload, data) -> {:ok, :unlocked, data + 1}
    (:unlocked, :push, _payload, data) -> {:ok, :locked, data}
    (:unlocked, :coin, _payload, data) -> {:ok, :unlocked, data + 1}
    (_, _, _, data) -> {:ok, :__same__, data}
```

The `on_transition` block contains pattern-matching clauses on
`(current_state, event, event_payload, state_payload)` and returns
`{:ok, next_state, new_payload}`. This keeps both the transition graph
and the transition logic in the same `.cure` file -- inspired by
Finitomata's approach.

This compiles to `:\"Cure.FSM.Turnstile\"`, a `GenServer`-based module
with `start_link/0,1`, `send_event/2`, `get_state/1`, `transitions/0`,
`allowed?/2`, and `responds?/2`.
`start_link/1` accepts custom initial data (e.g. `0` for the counter).

## Project Structure

```
cure_turnstile/
  cure_src/
    turnstile.cure          -- FSM definition
  lib/
    cure_turnstile.ex       -- GenServer wrapper with coin/passage tracking
    cure_turnstile/
      application.ex        -- OTP Application
    mix/tasks/
      compile_cure.ex       -- Mix task to compile .cure sources
  test/
    cure_turnstile_test.exs -- Tests for raw FSM and wrapper
```

## Usage

```bash
# Fetch dependencies
mix deps.get

# Compile (runs .cure compilation first, then Elixir)
mix compile

# Run tests
mix test

# Interactive session
iex -S mix

iex> {:ok, t} = CureTurnstile.start_link()
iex> CureTurnstile.insert_coin(t)
iex> CureTurnstile.push(t)
iex> CureTurnstile.stats(t)
%{state: :locked, coins: 1, passages: 1}
```
