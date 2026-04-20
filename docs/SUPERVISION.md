# Typed Supervision Trees
Cure 0.25.0 introduces typed actors, supervision trees, and a typed
send operator --- the Melquiades Operator --- on top of OTP.

The surface consists of four pieces:

1. The Melquiades Operator `<-|` (unicode alias `✉`) for sending a
   message to a pid.
2. `actor` containers that compile to OTP `GenServer` modules with
   exhaustiveness-checked message handlers.
3. `sup` containers that compile to OTP `Supervisor` behaviour modules
   with compile-time structural verification.
4. Stdlib modules `Std.Actor`, `Std.Process`, `Std.Supervisor` that
   expose the runtime from Cure source.

Together they turn Cure into a first-class language for writing
supervision trees without dropping into Elixir or Erlang.

## The Melquiades Operator
`pid <-| message` sends `message` to `pid`. The ASCII spelling and
its unicode alias are interchangeable:
```
pid <-| :hello
pid ✉  :hello
```
Both forms lower to Erlang's `!` operator, so the runtime semantics
are identical to `erlang:send/2`: the call is non-blocking, returns
the message it sent, and never raises for a dead receiver.

The operator is a statement expression, so it chains cleanly:
```
let ack = actor_pid <-| {:ping, self()}
```
The name "Melquiades" honors the ghost-mailman of *One Hundred Years
of Solitude*, who keeps delivering letters even after his own death.
The arrow points into the inbox on the left: `pid <-| message` reads
"the pid gets this message".

The operator is `non-associative` and binds one notch below `|>`, so
pipelines feed into sends naturally:
```
request
|> encode()
|> actor_pid <-| _          # equivalent to actor_pid <-| encode(request)
```
### Keyword form
`send pid, message` is a synonymous statement form kept for
backward compatibility and for `Std.Fsm` clients. It desugars to the
same `{:send, ...}` MetaAST node as `<-|`, so round-trip printing
preserves the original form.

## Actors
An `actor` container declares a typed process:
```
actor Counter with 0
  on_start
    (state) -> state
  on_message
    (:inc, n)   -> n + 1
    (:dec, n)   -> n - 1
    (:get, n)   -> notify({:value, n}); n
  on_stop
    (reason, _state) -> notify({:stopped, reason})
```
* `with <expr>` seeds the actor's initial payload. Omit it and the
  payload starts as `nil`.
* `on_start/on_message/on_stop` each accept one or more clauses; the
  clause syntax mirrors `on_transition` in FSMs. The first argument
  of an `on_message` clause is the inbox message, the second is the
  current payload.
* Inside any clause, `notify(message)` sends to the process that
  spawned the actor. `actor_self()` returns the actor's own pid.
* The return value of an `on_message` clause becomes the actor's new
  payload. Returning a plain `%Cure.Actor.State{}` struct replaces
  the entire runtime state instead.

Each `actor Counter` container compiles to a loaded BEAM module
named `Cure.Actor.Counter`. The module is a regular `GenServer`:
```
iex> :"Cure.Actor.Counter".start_link(0)
{:ok, #PID<...>}
iex> send(pid, :inc)
iex> :"Cure.Actor.Counter".get_state(pid)
1
```
For user code, prefer `Std.Actor.spawn/1` and the `<-|` operator:
```
let pid = Std.Actor.spawn(:"Cure.Actor.Counter")
pid <-| :inc
pid <-| :inc
let current = Std.Actor.get_state(pid)      # => 2
let _       = Std.Actor.stop(pid)
```
### Inbox types (preview)
The type system reserves `Pid(Inbox)` and `Ref` primitives so future
releases can extend the checker to unify message types against the
receiver's declared inbox. Today, `Pid` alone elaborates to
`{:pid, :any}`, which is the safe top of the covariant `Pid` family:
everything accepted by any inbox is accepted by `Pid`, so existing
FFI code keeps type-checking.

## Supervisors
A `sup` container declares a supervisor module:
```
sup App.Root
  strategy  = :one_for_one
  intensity = 3
  period    = 5
  children
    Counter as counter
    Counter as counter_b (restart: :transient)
    App.External as external (restart: :permanent, shutdown: 10000)
    sup Workers as workers
```
Settings (`strategy`, `intensity`, `period`) are top-level assignments
within the body and default to `:one_for_one`, `3`, and `5`. The
`children` block introduces one child spec per line.

A child spec takes the form:
```
Module as child_id
Module as child_id (restart: ..., shutdown: ..., kind: ...)
```
The module path is resolved with two conventions and one escape
hatch:

* A dotted module path (`App.Gateway`) is used as-is and becomes the
  atom `:"App.Gateway"`.
* An undotted name (`Counter`) resolves to `:"Cure.Actor.Counter"`
  (for workers) or `:"Cure.Sup.Counter"` (for a child introduced with
  `sup Name as id`).
* Prefix the child with the soft keyword `sup` to flip the default
  from worker to supervisor lookup: `sup Workers as workers`.

The supervisor compiler runs `Cure.Sup.Verifier` automatically.
Verification checks:

* Strategy is one of the four recognised atoms.
* Intensity is a non-negative integer.
* Period is a positive integer.
* All child ids are unique within the supervisor.
* Each child spec's `restart` (if specified) is one of
  `:permanent`, `:transient`, `:temporary`.
* Each child spec's `shutdown` is `:brutal_kill`, `:infinity`, or a
  positive integer.
* The supervisor does not list itself as a direct child
  (trivial cycle).

A verification failure stops codegen with a
`{:codegen_error, {:sup_verification_failed, errors}}` result; see
the error codes below.

## Runtime
`Cure.Sup.Runtime` wraps the compiled modules with a small
ETS-backed registry so a tree can be reached by module atom. The
table is created lazily on first use:
```
{:ok, _pid} = Cure.Sup.Runtime.start(:"Cure.Sup.App.Root")
Cure.Sup.Runtime.which_children(:"Cure.Sup.App.Root")
:ok = Cure.Sup.Runtime.stop(:"Cure.Sup.App.Root")
```
From Cure, use `Std.Supervisor`:
```
let tree = :"Cure.Sup.App.Root"
let _pid = Std.Supervisor.start(tree)
let kids = Std.Supervisor.which_children(tree)
let _    = Std.Supervisor.stop(tree)
```
Actor instances live in `Cure.Actor.Runtime`, a GenServer supervised
by `Cure.Supervisor`. It tracks spawned actors, auto-cleans up on
`DOWN`, and exposes `list_actors/0` for introspection.

## Links and Monitors
`Std.Process` exposes the raw BEAM process primitives directly:

* `link/1`, `unlink/1`
* `monitor/1` -> returns a `Ref`
* `demonitor/1`
* `trap_exit/1`
* `exit/2`
* `self/0`, `is_alive/1`

`link` / `monitor` / `trap_exit` go through small wrappers in
`Cure.Process.Builtins` so the Cure signatures can stay idiomatic
(`(Pid) -> Ref` rather than the two-argument erlang BIFs).

## Error codes
The new codes are catalogued in `Cure.Compiler.Errors`:

* **E045 Untyped Send** --- `<-|` on a bare `Pid` in strict mode.
* **E046 Inbox Mismatch** --- message not a subtype of the pid's inbox.
* **E047 Supervisor Unknown Child** --- child resolves to no module.
* **E048 Supervisor Cycle** --- supervisor references itself.
* **E049 Actor Handler Non-Exhaustive** --- `on_message` misses an
  inbox variant.
* **E050 Invalid Supervisor Strategy** --- unknown strategy, restart,
  or shutdown.

Run `cure explain E048` (or any code) for the full catalog text.

## Example
See `examples/cure_colony/` for a working supervision tree: a root
supervisor, a gateway actor, and a pair of worker actors that
exchange messages through `<-|`.
