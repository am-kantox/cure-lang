# cure_moneta

A money and ledger library written in Cure. The domain is deliberately simple
(everyone understands money) so the reader can focus on the language rather
than the problem. Yet the domain is semantically rich enough to motivate every
feature Cure offers: invariants that must hold across currencies, arithmetic
that fails at type-check time when misused, state machines with strict
lifecycle rules, and pure functional updates that leave the original value
untouched.

## Quick start

```bash
cd examples/cure_moneta
mix deps.get
mix test
```

## Feature walkthrough

### Multi-line ADT and pattern exhaustiveness (`moneta.cure:63`)

```cure
type Currency =
  | EUR
  | USD
  | GBP
  | JPY
  | CHF
  | OMR
```

The multi-line `|` form (v0.21.0) keeps each constructor on its own line
without needing a closing delimiter. Because every `match` on `Currency` must
cover all six variants, the type checker enforces exhaustiveness at compile
time. `show_currency` is the canonical example:

```cure
fn show_currency(c: Currency) -> String =
  match c
    EUR() -> "EUR"
    USD() -> "USD"
    GBP() -> "GBP"
    JPY() -> "JPY"
    CHF() -> "CHF"
    OMR() -> "OMR"
```

Adding a seventh currency without updating this function is a compile-time
error, not a silent runtime `nil`.

Note: nullary ADT constructors require `()` in both construction (`EUR()`) and
pattern (`EUR()`) positions. Bare `EUR` in a pattern is a variable binding that
matches any value, not a constructor match.

### Records and functional update (`moneta.cure:81`)

```cure
rec Money
  amount: Int            # minor units (cents for EUR, fils for OMR, ...)
  currency: Currency
  fractional_units: Int  # minor units per major unit: EUR=100, JPY=1, OMR=1000

rec Account
  id: Int
  owner: String
  balance: Money

rec Ledger
  accounts: List(Account)
```

Records compile to BEAM maps with a `__struct__` discriminator. All mutations
use the functional-update syntax that produces a fresh copy:

```cure
Ok(Money{a | amount: a.amount + b.amount})
Ok(update_account(ledger, Account{account | balance: new_balance}))
```

The `fractional_units` field carries the rendering and rounding semantics
directly in the value. `show` always knows how many decimal places to print,
and `convert` knows how to round the cross-currency result, because both pieces
of information travel with the `Money`.

### Refinement types and SMT verification (`moneta.cure:47`)

```cure
type PositiveAmount = {a: Int | a > 0}
type NonNegAmount   = {a: Int | a >= 0}
type Rate           = {r: Float | r > 0.0}
```

The Z3 solver proves at compile time that `PositiveAmount <: NonNegAmount`
(every integer greater than zero is also non-negative), and that `Rate` is
satisfiable (r = 1.0 is a witness). The `scale` function uses an inline
refinement type as a parameter:

```cure
fn scale(m: Money, factor: {n: Int | n > 0}) -> Money =
  Money{m | amount: m.amount * factor}
```

A caller who passes 0 or a negative factor gets a type error, not a silently
wrong result.

### Protocols for record types (`moneta.cure:100`)

`proto Show(T)` and `proto Eq(T)` are defined locally in `moneta.cure`. Their
implementations for `Money` demonstrate guard-based dispatch on user-defined
record types:

```cure
impl Show for Money
  fn show(m: Money) -> String =
    let sign = if m.amount < 0 then "-" else ""
    ...

impl Eq for Money
  fn eq(a: Money, b: Money) -> Bool =
    a.currency == b.currency and a.amount == b.amount
```

Protocol dispatch compiles to a guard-based multi-clause BEAM function. For
record types the guard checks `is_map(V) andalso map_get('__struct__', V) == money`.
`fractional_units` is excluded from `eq`: two `Money` values with the same
currency and minor-unit count are equal regardless of how many decimal places
they display.

### ADT rendering without protocol dispatch (`moneta.cure:120`)

`Currency` is an ADT and compiles to Erlang tagged tuples (`{eur}`, `{usd}`,
...), not maps. The `is_map` guard in protocol dispatch would never match a
tuple, so `Currency` uses a plain function instead of a protocol implementation:

```cure
fn show_currency(c: Currency) -> String =
  match c
    EUR() -> "EUR"
    ...
```

`impl Show for Money` calls `show_currency(m.currency)` internally. The
protocol still dispatches on `Money`; the rendered currency name comes from
the plain function. This is an honest demonstration of where Cure's current
protocol system applies and where a direct `match` expression is the right tool.

### @extern FFI (`moneta.cure:19`)

Cure's `/` operator lowers to Erlang integer `div`. Real float division and
int-to-float promotion come from the host via `@extern`:

```cure
@extern(Elixir.CureMoneta.Math, :fdiv, 2)
local fn fdiv(a: Float, b: Float) -> Float

@extern(Elixir.CureMoneta.Math, :int_to_float, 1)
local fn int_to_float(n: Int) -> Float

@extern(:erlang, :round, 1)
local fn float_round(f: Float) -> Int
```

`CureMoneta.Math` is a three-line Elixir module. All other FFI targets
(`:erlang.abs`, `:erlang.integer_to_binary`, `:binary.copy`) are Erlang BIFs
called without an Elixir shim. The FX conversion then reads as pure Cure:

```cure
fn convert(m: Money, to: Currency, rate: Rate, new_fractional_units: Int) -> Money =
  let amount_f = int_to_float(m.amount)
  let converted = float_round(amount_f * rate)
  Money{amount: converted, currency: to, fractional_units: new_fractional_units}
```

### Result chaining without exceptions (`moneta.cure:255`)

No function raises; every fallible operation returns `Result(T, String)`.
`transfer` shows the short-circuit chain:

```cure
fn transfer(ledger: Ledger, from_id: Int, to_id: Int, amount: Money) -> Result(Ledger, String) =
  match withdraw(ledger, from_id, amount)
    Error(e) -> Error(e)
    Ok(after_withdraw) -> deposit(after_withdraw, to_id, amount)
```

The ledger is never partially updated: if the withdrawal succeeds but the
deposit fails (e.g. currency mismatch), the function returns `Error` and the
original ledger is unmodified.

### First-class FSM (`transaction.cure`)

```cure
fsm Transaction with Int
  Idle        --create-->    Pending
  Pending     --submit-->    Submitting
  Submitting  --dispatch!--> Awaiting
  Awaiting    --confirm-->   Settled
  Awaiting    --reject-->    Failed
  Failed      --retry?-->    Pending
  *           --cancel?-->   Cancelled
```

Three distinct event kinds appear in one FSM:

**Hard event `dispatch!`** -- `Submitting` has exactly one outgoing event, so
`dispatch!` auto-fires the instant the FSM enters that state. No caller needs
to send it; the Cure compiler verifies the sole-outgoing-event constraint and
would reject the definition if a second outgoing event were added from
`Submitting`.

**Soft event `retry?`** -- the `?` suffix means the event succeeds silently
without logging or calling `on_failure` when no valid transition exists from
the current state (e.g. `retry` from `Awaiting` or `Settled`). A normal event
in the same situation would call `on_failure`.

**Soft wildcard `* --cancel?-->`** -- the wildcard means every state has a
`cancel` transition, so `cancel` always fires. The `?` suffix would make it
degrade gracefully if a clause were ever missing.

### FSM lifecycle callbacks (`transaction.cure:42`)

```cure
  on_enter
    (:awaiting, _) -> :ok
    (:settled, _)  -> :ok
    (:failed, _)   -> :ok
    (_, _)         -> :ok

  on_failure
    (_, _, _) -> :ok

  on_timer
    (:awaiting, _) -> %[:transition, :reject, 0]
    (_, _)         -> :ok
```

`on_timer` fires every 30 seconds (`@timer 30000`). From `:awaiting` it returns
`{:transition, :reject, 0}`, which the FSM runtime interprets as "fire the
`:reject` event with payload 0", moving the transaction to `:failed`
automatically. From any other state it returns `:ok` (no-op). This prevents
a transaction from blocking indefinitely if the payment processor never
responds.

`on_failure` is called when a non-soft event has no valid target from the
current state. `on_enter` fires after every state entry and is where
instrumentation or side-effects belong.

### Callback-mode FSM with `on_transition` (`transaction.cure:55`)

```cure
  on_transition
    (:idle,       :create,   _payload, _data) -> %[:ok, :pending,    0]
    (:pending,    :submit,   _payload,  data) -> %[:ok, :submitting, data]
    (:submitting, :dispatch, _payload,  data) -> %[:ok, :awaiting,   data]
    (:awaiting,   :confirm,  _payload,  data) -> %[:ok, :settled,    data]
    (:awaiting,   :reject,   _payload, _data) -> %[:ok, :failed,     0]
    (:failed,     :retry,    _payload, _data) -> %[:ok, :pending,    0]
    (_,           :cancel,   _payload,  data) -> %[:ok, :cancelled,  data]
    (_,           _,         _,         data) -> %[:ok, :__same__,   data]
```

The presence of an `on_transition` block activates callback mode: the FSM
compiles to a `GenServer`-based BEAM module (`Cure.FSM.Transaction`) rather
than a `gen_statem` module. Every state transition calls the matching clause.
The return tuple `%[:ok, next_state, new_payload]` drives both the state
change and the data update. `:__same__` keeps the current state while still
allowing the payload to change.

Note that the event name in `on_transition` is the base name after stripping
the suffix: `dispatch` not `dispatch!`, `retry` not `retry?`, `cancel` not
`cancel?`. The `!`/`?` suffixes are a transition-graph annotation, not part of
the event atom.

### OTP interop (`lib/`)

`CureMoneta.Application` starts two children under a supervisor:

`CureMoneta.LedgerServer` is a `GenServer` whose state is the Cure `Ledger`
map. All computation is delegated to `Cure.Moneta`:

```elixir
def handle_call({:deposit, id, amount}, _from, ledger) do
  case @moneta.deposit(ledger, id, amount) do
    {:ok, new_ledger} -> {:reply, :ok, new_ledger}
    {:error, _} = err -> {:reply, err, ledger}
  end
end
```

`CureMoneta.TxSupervisor` is a `DynamicSupervisor` under which each call to
`CureMoneta.begin_transaction/0` spawns a fresh `Cure.FSM.Transaction`
GenServer with a transient restart strategy.

The Cure BEAM modules are loaded from `_build/cure/ebin/` at runtime. The
Elixir wrapper uses `@compile {:no_warn_undefined, module}` to silence the
"module not available at compile time" diagnostic, following the same pattern
as `cure_spline`.

## Project layout

```
cure_src/
  moneta.cure       -- all core Cure code: types, records, protocols, arithmetic,
                       FX conversion, ledger mutations (292 lines)
  transaction.cure  -- payment transaction FSM: 7 states, 3 event kinds,
                       on_enter / on_failure / on_timer / on_transition (63 lines)
lib/
  cure_moneta.ex              -- public Elixir API (money/2,3, show, eq,
                                 add, subtract, scale, convert, ledger ops,
                                 begin_transaction, tx_event, tx_state)
  cure_moneta/
    application.ex            -- OTP Application (LedgerServer + TxSupervisor)
    ledger_server.ex          -- GenServer wrapping the Cure Ledger
    math.ex                   -- float FFI helpers (fdiv/2, int_to_float/1)
test/
  cure_moneta_test.exs        -- 64 cases: raw Cure.Moneta module, raw
                                 Cure.FSM.Transaction FSM, CureMoneta wrapper
```

## Amount encoding

All amounts are stored in **minor units** -- the smallest indivisible
denomination for a currency. `fractional_units` is not derived from the
currency code at runtime; it is stored in the `Money` record so the library
can support any currency without a lookup table.

| Currency | `fractional_units` | Example |
|---|---|---|
| EUR, USD, GBP, CHF | 100 | EUR 1.00 = `amount: 100` |
| JPY | 1 | JPY 500 = `amount: 500` |
| OMR | 1000 | OMR 1.000 = `amount: 1000` |

## Transaction FSM state diagram

```
Idle --create--> Pending --submit--> Submitting
                                          |
                                     dispatch!   (hard: auto-fires on entry;
                                          |        sole outgoing event from Submitting)
                                          v
                              +----> Awaiting
                              |       /     \
                           on_timer confirm  reject
                           (30 s)    |        |
                              |      v        v
                              +-- Failed   Settled
                                    |
                                  retry?    (soft: silent no-op from other states)
                                    |
                                  Pending

* --cancel?--> Cancelled   (wildcard soft: fires from every state)
```

## Example session

```elixir
# (Application starts automatically under mix test / mix run)

# -- Money values -----------------------------------------------------------
eur100 = CureMoneta.money(:eur, 10_000)   # EUR 100.00  (10_000 cents)
omr1   = CureMoneta.money(:omr,  1_000)   # OMR   1.000 ( 1_000 baisa)
jpy500 = CureMoneta.money(:jpy,    500)   # JPY 500

CureMoneta.show(eur100)   #=> "EUR 100.00"
CureMoneta.show(omr1)     #=> "OMR 1.000"
CureMoneta.show(jpy500)   #=> "JPY 500"

# Currency ADT rendered via plain function (not protocol dispatch):
CureMoneta.show_currency({:eur})   #=> "EUR"

# -- Arithmetic -------------------------------------------------------------
{:ok, sum}    = CureMoneta.add(eur100, CureMoneta.money(:eur, 50))
CureMoneta.show(sum)   #=> "EUR 100.50"

{:error, msg} = CureMoneta.add(eur100, jpy500)
# msg: "currency mismatch: cannot add EUR and JPY"

# -- FX conversion ----------------------------------------------------------
usd108 = CureMoneta.convert(eur100, :usd, 1.08)
CureMoneta.show(usd108)   #=> "USD 108.00"

# -- Ledger -----------------------------------------------------------------
:ok = CureMoneta.open_account(1, "Alice", :eur, 50_000)   # EUR 500.00
:ok = CureMoneta.open_account(2, "Bob",   :eur,  5_000)   # EUR  50.00
:ok = CureMoneta.transfer(1, 2, :eur, 10_000)
{:ok, bal} = CureMoneta.balance(2)
CureMoneta.show(bal)   #=> "EUR 150.00"

# -- Transaction FSM --------------------------------------------------------
{:ok, pid} = CureMoneta.begin_transaction()
CureMoneta.tx_event(pid, :create)
CureMoneta.tx_event(pid, :submit)
# dispatch! auto-fires; FSM moves Submitting -> Awaiting without a manual event
CureMoneta.tx_state(pid)   #=> {:awaiting, 0}
CureMoneta.tx_event(pid, :confirm)
CureMoneta.tx_state(pid)   #=> {:settled, 0}
```
