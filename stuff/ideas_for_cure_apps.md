# Ideas for exemplary Cure example projects

The existing `cure_spline` covers numerics + refinement types + records well, but
stays in a single quadrant: pure math, no FSMs, no ADTs, no protocols. The ideas
below are ranked by how comprehensively they exercise Cure's distinctive features
while remaining easy to read at a glance.

---

## 1. cure_brainloop (top pick, to implement next)

A toy but complete expression-language interpreter with a REPL driven by a Cure FSM.

### Why it is ideal

It is the only candidate that uses *every* Cure feature in a natural way, stays
under ~600 lines of Cure, and every reader immediately recognises the shape
("lexer -> parser -> evaluator -> REPL, with a state machine tying it together").
The narrative arc mirrors Cure's own compiler pipeline, giving readers a
satisfying meta-resonance.

### Feature coverage

- **ADT** -- `Expr = Num(Int) | Var(Atom) | BinOp(Op, Expr, Expr) | Let(...)
  | If(...)`: exercises ADTs + pattern exhaustiveness.
- **Records** -- `Env{bindings: ...}` for variable scope; `Std.Access` lenses
  for nested scope mutation.
- **Refinement types** -- `Stack{n: Nat}` with `push: Stack{n} -> Int ->
  Stack{n+1}`, `pop: Stack{n+1} -> (Int, Stack{n})`; SMT proves push/pop balance.
- **Protocols** -- `Show` for values, `Eval` dispatched per AST node.
- **Effect annotations** -- `eval(...) ! Exception`, `repl_loop(...) ! Io, Exception`.
- **FSM** -- REPL lifecycle: `Idle -> Reading -> Parsing -> Evaluating ->
  Printing -> Idle`, `:error` to `Recovering`; `quit!` as a hard event,
  `blank?` as a soft event; `gen_statem` mode.
- **OTP interop** -- FSM started under supervision; Elixir wrapper exposes
  `eval/1`; Mix escript `cure_brainloop repl`.
- **FFI** -- `@extern` to `:io.get_line/1`.
- **Stdlib** -- List, Result, Show, Io, Access.

---

## 2. cure_moneta (to implement now)

A money and ledger library: currency arithmetic, FX conversion, and a ledger
GenServer with a transaction-lifecycle FSM.

### Why this slot

Easy domain (everyone groks "money"), strong on refinement types for business
invariants, OTP-friendly FSM, natural use of protocols and records. Weaker on
parser/AST territory, which is fine -- that is cure_brainloop's job.

### Feature coverage

- **ADT** -- `Currency = EUR | USD | GBP | JPY | CHF`; `TxResult = Settled |
  Reversed | Cancelled`.
- **Records** -- `Money{amount: Int, currency: Currency}`,
  `Account{id: Int, owner: String, balance: Money}`,
  `Ledger{accounts: List(Account)}`.
- **Refinement types** -- `PositiveAmount = {a: Int | a > 0}` for deposits;
  `Rate = {r: Float | r > 0.0}` for FX rates; ensures non-negative balances
  at the type level.
- **Protocols** -- `Show` for `Currency` and `Money`; `Eq` for same-currency
  comparison; exhaustiveness on `Currency` ADT in every `match`.
- **Result error handling** -- `add`, `subtract`, `transfer`, `convert` all
  return `Result(Money, String)` or `Result(Ledger, String)`.
- **FSM -- transaction lifecycle**:
  - `Idle -> Pending -> Submitting -> Awaiting -> Settled | Failed`
  - `dispatch!` is a hard event that auto-fires when entering `Submitting`
    (sole outgoing event).
  - `retry?` is a soft event (silently no-ops from `Settled`).
  - `* --cancel?--> Cancelled` is a wildcard soft event.
  - `on_timer` on `Awaiting` fires an auto-reject after a configurable timeout.
  - `on_enter` / `on_failure` for logging.
  - `on_transition` callback mode produces a GenServer module.
- **FFI** -- `@extern` to a small Elixir helper for float division (needed for
  FX rate calculations, same pattern as cure_spline).
- **OTP** -- `LedgerServer` GenServer wraps the ledger state; the transaction
  FSM runs under a `DynamicSupervisor`; both are started by
  `CureMoneta.Application`.
- **Stdlib** -- `Std.List` for account lookup, `Std.String` for formatting,
  `Std.Math` for rounding, `Std.Result`.

### Planned file layout

```
examples/cure_moneta/
  mix.exs
  .formatter.exs
  .gitignore
  README.md
  cure_src/
    moneta.cure          -- Currency ADT, Money record, Account, Ledger,
                            Show + Eq protocols, arithmetic, FX, ledger ops
    transaction.cure     -- Transaction FSM (hard/soft events, on_timer)
  lib/
    cure_moneta.ex                -- public Elixir API
    cure_moneta/
      application.ex              -- OTP Application
      ledger_server.ex            -- GenServer over Ledger
      math.ex                     -- FFI float helpers (fdiv, round_to_cents)
  test/
    test_helper.exs
    cure_moneta_test.exs          -- ExUnit suite: raw Cure module, FSM, wrapper
```

---

## 3. cure_vending

A vending machine controller. Bigger FSM than the turnstile, with coin/bill
acceptance, product selection, change-making, and a maintenance mode.

- Hard events (`service!`, `reset!`) and soft events (`coin?`).
- `on_timer` drives the "insert coin within 30s" timeout.
- `on_failure` handles stuck dispense.
- Records for `Product{sku, name, price}`, `Coin{denom}`.
- ADT for `DispenseResult`.
- `Show` for inventory.

Hits FSM + records + refinement beautifully; weaker on parser/AST territory.

---

## 4. cure_moneta variant -- cure_raftlite / cure_tcp_sm

Connection-oriented protocols (TCP handshake, or cut-down Raft leader election)
showcase hard/soft events, `on_timer`, and `Cure.FSM.Verifier` proving
reachability on something that actually matters. Domain complexity likely
overshoots "easily grasped".

---

## 5. cure_regex

Thompson NFA construction. ADT for the regex AST, NFA simulation as a natural
FSM, refinement on capture-group indices, `Show` for pretty-print. Beautiful but
the NFA part is subtle; non-PL readers may not follow at a glance.
