# cure_moneta

A money and ledger library written in Cure, demonstrating the breadth of the
language in a domain every reader grasps immediately.

## Features demonstrated

| Cure feature | Where |
|---|---|
| Multi-line ADT | `Currency = EUR \| USD \| GBP \| JPY \| CHF \| OMR` |
| Refinement types | `PositiveAmount`, `Rate` (SMT-checked by Z3) |
| Records | `Money{amount, currency, fractional_units}`, `Account`, `Ledger` |
| `fractional_units` field | Enables correct rendering for EUR (100), JPY (1), OMR (1000) |
| Show protocol | Currency and Money implementations; pattern exhaustiveness on all 6 variants |
| Eq protocol | Same-currency, same-amount Money equality |
| Result chaining | `deposit`, `withdraw`, `transfer` all return `Result(_, String)` |
| `@extern` FFI | `fdiv/2`, `int_to_float/1` from `CureMoneta.Math`; `round/1`, `abs/1` from `:erlang` |
| Hard FSM event | `dispatch!` auto-fires from `Submitting` (sole outgoing) |
| Soft FSM events | `retry?`, `cancel?` -- silently ignored from invalid states |
| Wildcard transition | `* --cancel?--> Cancelled` |
| `on_timer` | Auto-rejects a stuck `Awaiting` transaction after 30 s |
| `on_enter`, `on_failure` | Lifecycle callbacks in callback-mode FSM |
| `on_transition` | Callback-mode GenServer FSM with per-clause handlers |
| OTP interop | `LedgerServer` GenServer + `DynamicSupervisor` for transactions |

## Project layout

```
cure_src/
  moneta.cure       -- Currency, Money, Account, Ledger; Show/Eq protocols;
                       arithmetic, FX conversion, ledger mutations
  transaction.cure  -- Payment transaction FSM (7 states, 3 event kinds)
lib/
  cure_moneta.ex              -- public Elixir API
  cure_moneta/
    application.ex            -- OTP application
    ledger_server.ex          -- GenServer wrapping the Cure Ledger
    math.ex                   -- float FFI helpers
test/
  cure_moneta_test.exs        -- 40+ cases: raw Cure module, raw FSM, wrapper
```

## Amount encoding

All amounts are stored in **minor units** (the smallest indivisible unit):

| Currency | `fractional_units` | Example |
|---|---|---|
| EUR, USD, GBP, CHF | 100 | EUR 1.00 = `amount: 100` |
| JPY | 1 | JPY 500 = `amount: 500` |
| OMR | 1000 | OMR 1.000 = `amount: 1000` |

## Quick start

```bash
cd examples/cure_moneta
mix deps.get
mix test
```

## Example session (Elixir IEx)

```elixir
# Start the application (done automatically by mix run / mix test)
{:ok, _} = Application.ensure_all_started(:cure_moneta)

# Create Money values
eur100 = CureMoneta.money(:eur, 10_000)   # EUR 100.00
omr1   = CureMoneta.money(:omr, 1_000)    # OMR 1.000
jpy500 = CureMoneta.money(:jpy, 500)      # JPY 500

CureMoneta.show(eur100)   # => "EUR 100.00"
CureMoneta.show(omr1)     # => "OMR 1.000"

# FX conversion: EUR -> USD at 1.08
usd = CureMoneta.convert(eur100, :usd, 1.08)
CureMoneta.show(usd)      # => "USD 108.00"

# Ledger operations
:ok = CureMoneta.open_account(1, "Alice", :eur, 50_000)   # EUR 500.00
:ok = CureMoneta.open_account(2, "Bob",   :eur,  5_000)   # EUR 50.00
:ok = CureMoneta.transfer(1, 2, :eur, 10_000)             # Alice sends EUR 100
{:ok, bal} = CureMoneta.balance(2)
CureMoneta.show(bal)      # => "EUR 150.00"

# Transaction FSM
{:ok, pid} = CureMoneta.begin_transaction()
CureMoneta.tx_event(pid, :create)
CureMoneta.tx_event(pid, :submit)
# dispatch! fires automatically (hard event)
CureMoneta.tx_state(pid)  # => {:awaiting, 0}
CureMoneta.tx_event(pid, :confirm)
CureMoneta.tx_state(pid)  # => {:settled, 0}
```

## Transaction FSM state diagram

```
Idle --create--> Pending --submit--> Submitting --dispatch!--> Awaiting
                                                               |       |
                                                           confirm   reject
                                                               |       |
                                                           Settled   Failed --retry?--> Pending
* --cancel?--> Cancelled  (from any state; soft: ignored from terminal states)
```

`on_timer` fires every 30 s; when in `Awaiting`, it immediately sends a
`:reject` event to prevent indefinite blocking.
