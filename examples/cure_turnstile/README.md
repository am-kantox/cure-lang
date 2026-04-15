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
fsm Turnstile
  Locked   --coin do data + 1--> Unlocked
  Unlocked --push--> Locked
  Unlocked --coin do data + 1--> Unlocked
  Locked   --push--> Locked
```

The `do` blocks mutate the FSM's state data during transitions. Here
`data` refers to the current value and the expression produces the new
value. Each `coin` event increments the counter; `push` leaves it
unchanged.

This compiles to `:\"Cure.FSM.Turnstile\"`, a full OTP `gen_statem` with
`start_link/0`, `start_link/1`, `send_event/2`, and `get_state/1`.
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
