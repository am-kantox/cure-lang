%{
  title: "Actors",
  description: "Typed supervision trees with first-class actor and sup containers, the Melquiades send operator (<-|), links, monitors, and trap_exit.",
  order: 5
}
---
Cure 0.25.0 turns the language into a first-class environment for writing OTP-style supervision trees. The four pieces that land together are:

1. The **Melquiades Operator** `<-|` (unicode alias `✉`) for sending a message to a pid.
2. `actor` containers that compile to loaded `GenServer` modules with exhaustiveness-checked message handlers.
3. `sup` containers that compile to verified `Supervisor` behaviour modules with compile-time structural checks.
4. Stdlib modules `Std.Actor`, `Std.Process`, `Std.Supervisor` that expose the runtime to Cure source.

Together they let you declare a production-grade supervision tree without ever dropping into Elixir or Erlang.

## The Melquiades Operator

`pid <-| message` sends `message` to `pid` and evaluates to the message, matching Erlang's `!` semantics. The ASCII spelling and its unicode alias are interchangeable:

```cure
pid <-| :hello
pid ✉  :hello
```

Both forms lower to Erlang's bang operator (`{:op, Line, :!, PidForm, MsgForm}` in abstract form), so the runtime cost is exactly the same as a bare `erlang:send/2`: non-blocking, returns the message it sent, never raises for a dead receiver.

The operator is **non-associative** and binds one notch below `|>` so pipelines feed into it naturally:

```cure
request
|> encode()
|> worker_pid <-| _
```

The last line is equivalent to `worker_pid <-| encode(request)`.

### Why "Melquiades"?

Named after the ghost-mailman of *One Hundred Years of Solitude*, who keeps delivering letters even after his own death. The arrow points into the inbox on the left: `pid <-| message` reads "the pid gets this message".

### Keyword form

`send target, msg` is a synonymous statement form retained for backward compatibility and for `Std.Fsm` clients. It desugars to the same `{:send, …}` MetaAST node as `<-|`, so round-trip printing preserves the author's chosen spelling through a `:melquiades_form` meta key (`:ascii`, `:unicode`, or `:keyword`).

## Actors

An `actor` container declares a typed process. The minimal grammar:

```cure
actor Counter with 0
  on_start
    (state) -> state
  on_message
    (:inc, n)   -> n + 1
    (:dec, n)   -> n - 1
    (:get, n) ->
      notify(%[:value, n])
      n
  on_stop
    (reason, _state) -> notify(%[:stopped, reason])
```

- `with <expr>` seeds the actor's initial payload. Omit it and the payload starts as `nil`.
- `on_start`, `on_message`, `on_stop` each accept one or more clauses; the clause syntax mirrors `on_transition` in FSMs (pattern tuple + optional `when` guard + body).
- The first argument of an `on_message` clause is the incoming message; the second is the current payload.
- Inside any clause, `notify(message)` sends to the process that spawned the actor. The helper is wired through `Cure.Actor.State.notify_self/1`, which reads the actor's registered `:caller` from the process dictionary.
- The return value of an `on_message` clause becomes the actor's new payload. Returning a `%Cure.Actor.State{}` struct replaces the entire runtime state instead, exactly like callback-mode FSMs.

Each `actor Counter` container compiles to a loaded BEAM module named `Cure.Actor.Counter`. The module is a regular `GenServer`:

```elixir
iex> :"Cure.Actor.Counter".start_link(0)
{:ok, #PID<...>}
iex> send(pid, :inc)
iex> :"Cure.Actor.Counter".get_state(pid)
1
```

For user code, prefer `Std.Actor.spawn/1` together with the `<-|` operator:

```cure
let pid = Std.Actor.spawn(:"Cure.Actor.Counter")
pid <-| :inc
pid <-| :inc
let current = Std.Actor.get_state(pid)      # => 2
let _       = Std.Actor.stop(pid)
```

### Inbox types (preview)

The type system already reserves `Pid(Inbox)` and `Ref` primitives. `Pid` alone elaborates to `{:pid, :any}`, the top of the covariant `Pid` family: everything accepted by any inbox is accepted by `Pid`, so existing FFI code keeps type-checking. The send-site checker clause unifies the message type against the receiver's declared inbox and emits `E046 Inbox Mismatch` on conflict.

## Supervisors

A `sup` container declares a supervisor module:

```cure
sup App.Root
  strategy  = :one_for_one
  intensity = 3
  period    = 5
  children
    Counter               as counter
    Counter               as counter_b  (restart: :transient)
    App.External          as external   (restart: :permanent, shutdown: 10000)
    sup Workers           as workers
```

Settings (`strategy`, `intensity`, `period`) default to `:one_for_one`, `3`, and `5` respectively. The `children` block introduces one child spec per line.

Child specs take the form `Module as child_id` with an optional trailing parenthesised keyword list. The module path resolves with two conventions and one escape hatch:

- A dotted path (`App.Gateway`) is used verbatim and becomes the atom `:"App.Gateway"`.
- A bare name (`Counter`) resolves to `:"Cure.Actor.Counter"` by default (or `:"Cure.Sup.Counter"` for supervisor children).
- Prefix with the soft keyword `sup` to flip the default from worker to supervisor lookup: `sup Workers as workers`.

The supervisor compiler runs `Cure.Sup.Verifier` automatically. Verification enforces:

- `strategy` is one of `:one_for_one`, `:one_for_all`, `:rest_for_one`, `:simple_one_for_one`.
- `intensity` is a non-negative integer; `period` is a positive integer.
- All child ids are unique within the supervisor.
- Each `restart` (if specified) is one of `:permanent`, `:transient`, `:temporary`.
- Each `shutdown` is `:brutal_kill`, `:infinity`, or a positive integer.
- The supervisor does not list itself as a direct child.

A verification failure stops codegen with a `{:codegen_error, {:sup_verification_failed, errors}}` result and surfaces under error codes `E047`, `E048`, and `E050`.

### Soft keyword

`sup` is intentionally *not* reserved at the lexer level, so existing programs that use `sup` as a field name or local variable (for instance the superdiagonal row of a tridiagonal system in `examples/cure_spline`) keep compiling. The parser dispatches `sup <Name>` to the supervisor parser only at statement-prefix position when the next token is an identifier. In every other context, `sup` is a plain variable.

## Runtime

`Cure.Sup.Runtime` wraps the compiled supervisor modules with a lazy ETS-backed registry so a tree can be reached by module atom. The table is created on first use:

```elixir
{:ok, _pid} = Cure.Sup.Runtime.start(:"Cure.Sup.App.Root")
Cure.Sup.Runtime.which_children(:"Cure.Sup.App.Root")
:ok = Cure.Sup.Runtime.stop(:"Cure.Sup.App.Root")
```

From Cure, the equivalent is `Std.Supervisor`:

```cure
let tree = :"Cure.Sup.App.Root"
let _pid = Std.Supervisor.start(tree)
let kids = Std.Supervisor.which_children(tree)
let _    = Std.Supervisor.stop(tree)
```

Actor instances live in `Cure.Actor.Runtime`, a GenServer supervised by `Cure.Supervisor` and started automatically by the application. It tracks spawned actors in an ETS registry, monitors every pid, and cleans up on `DOWN`. `Cure.Actor.Runtime.list_actors/0` returns every live actor for introspection.

## Links, monitors, trap_exit

`Std.Process` exposes the raw BEAM process primitives directly:

```cure
mod MyApp.Pool
  use Std.Process

  fn watch(child: Pid) -> Ref =
    let _ = link(child)
    monitor(child)
```

The full surface:

- `link/1`, `unlink/1`
- `monitor/1` -> returns a `Ref`
- `demonitor/1`
- `trap_exit/1` (returns the previous value)
- `exit/2`
- `self/0`, `is_alive/1`

`monitor` and `trap_exit` go through small wrappers in `Cure.Process.Builtins` so the Cure signatures can stay idiomatic (`(Pid) -> Ref` rather than the two-argument erlang BIFs). Everything else is a direct `@extern(:erlang, ...)` call.

## Error codes

The new codes are catalogued in `Cure.Compiler.Errors`. Run `cure explain <code>` for the full text:

- **E045 Untyped Send** -- `<-|` on a bare `Pid` in strict mode.
- **E046 Inbox Mismatch** -- message not a subtype of the receiver's inbox ADT.
- **E047 Supervisor Unknown Child** -- child resolves to no compiled module.
- **E048 Supervisor Cycle** -- supervisor references itself transitively.
- **E049 Actor Handler Non-Exhaustive** -- `on_message` misses an inbox variant.
- **E050 Invalid Supervisor Strategy** -- unknown strategy, restart, or shutdown value.

## Full example

`examples/cure_colony/cure_src/colony.cure` ships with the release and exercises the whole surface: a worker actor, an echo actor, and a supervisor tree managing them under a `:one_for_one` strategy.

```cure
actor Worker with 0
  on_start
    (state) -> state
  on_message
    (:inc, n)   -> n + 1
    (:reset, _n) -> 0
    (:get, n) ->
      notify(%[:value, n])
      n

actor Echo with nil
  on_message
    (msg, _payload) ->
      notify(%[:echo, msg])
      msg

sup Colony
  strategy  = :one_for_one
  intensity = 3
  period    = 5
  children
    Worker as worker_a
    Worker as worker_b (restart: :transient)
    Echo   as echo     (restart: :permanent, shutdown: 2000)
```

See the on-disk reference [`docs/SUPERVISION.md`](https://github.com/am-kantox/cure-lang/blob/main/docs/SUPERVISION.md) for the full prose companion to this page.
