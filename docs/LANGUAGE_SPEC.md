# Cure Language Specification

## Syntax Overview

Cure is an indentation-structured language. Blocks are delimited by
indentation level, not by keywords like `do`/`end` or braces.

### Keywords

`fn`, `mod`, `rec`, `fsm`, `actor`, `proto`, `impl`, `type`, `let`, `if`,
`then`, `else`, `elif`, `match`, `when`, `where`, `local`, `use`, `return`,
`throw`, `try`, `catch`, `finally`, `for`, `in`, `true`, `false`, `nil`,
`and`, `or`, `not`, `spawn`, `send`, `receive`, `after`, `proof`, `extern`,
`end`, `do`

`sup` is a *contextual* soft keyword (v0.25.0): at the lexer level it is
an ordinary identifier so legacy code that uses it as a field or variable
name keeps compiling; the parser dispatches `sup <Name>` to the
supervisor container only at statement-prefix position.

`app` is a *contextual* soft keyword (v0.26.0) with the same treatment:
`app <Name>` at statement-prefix position opens an application
container; every other use of `app` remains a plain identifier.

### Identifiers

Identifiers may carry a trailing `?` to signal a predicate (Elixir
convention):

```cure
fn even?(n: Int) -> Bool = n % 2 == 0
fn is_empty?(xs: List(T)) -> Bool = ...
```

The `!` suffix is reserved for effect annotations and FSM hard
events.

### Comments and docstrings

- `# ...` -- line comment.
- `## text` -- single-line doc comment. One per line; attached to the
  following definition. Consecutive `##` blocks separated by a
  blank-line gap (or by plain `#` comments that the lexer drops) are
  merged into a single docstring with a paragraph break between
  blocks (v0.29.0: `Cure.Compiler.Parser.collect_all_doc_comments/1,2`).
  This lets you write a long docstring in natural paragraphs without
  leaving orphan `:doc_comment` tokens ahead of the next definition.
- `###\n...\n###` -- fenced multi-line doc comment. Opens on a line
  whose first three non-whitespace characters are `###`; closes on the
  next line whose first three non-whitespace characters are `###`.
  Leading indentation common to every body line is stripped.
- **Docstring body grammar.** Doc-comment bodies are Markdown: `cure`
  doc tooling (`Cure.Doc.Markdown`, `cure doc`, the REPL's `:doc` /
  `:help` output, and the Cure website's `/stdlib/:module` pages) pipe
  the body through the NIF-free `:md` library. Fenced code blocks
  carrying a known language (`cure`, `elixir`, `erlang`) are
  syntax-highlighted via Makeup; unknown languages pass through with a
  stable `language-<lang>` class for downstream CSS. The strings
  `{{cure_version}}` and `{{cure_vversion}}` are substituted for the
  running Cure version before parsing so release-sensitive copy can
  travel inside docstrings.

### Operators (by precedence, low to high)

- `|>` -- pipe (left-assoc)
- `<-|` / `✉` -- Melquiades send (non-assoc, v0.25.0); binds one notch
  below `|>` so `x |> encode |> pid <-| _` groups as
  `pid <-| (x |> encode)`
- `or` -- boolean or (left-assoc)
- `and` -- boolean and (left-assoc)
- `==`, `!=`, `<`, `>`, `<=`, `>=` -- comparison (non-assoc)
- `..`, `..=` -- range (non-assoc)
- `<>` -- string concat (right-assoc)
- `+`, `-` -- additive (left-assoc)
- `*`, `/`, `%` -- multiplicative (left-assoc)
- `-`, `not` -- unary prefix
- `.` -- field access (left-assoc)

### Literals

- Integers: `42`, `0xFF`, `0b1010`
- Floats: `3.14`
- Strings: `"hello"`, `"hello #{name}"`
- Booleans: `true`, `false`
- Atoms: `:ok`, `:error`
- Nil: `nil`
- Chars: `'a'`
- Lists: `[1, 2, 3]`, `[h | t]`
- Tuples: `%[a, b]`
- Maps: `%{key: value}`

## Modules

```cure
mod MyApp.Math
  fn add(a: Int, b: Int) -> Int = a + b
  local fn helper() -> Int = 42
```

All functions are public by default. Use `local fn` for private.

## Functions

### Single-expression body

```cure
fn add(a: Int, b: Int) -> Int = a + b
```

### Multi-expression body (indented block)

```cure
fn compute(x: Int) -> Int =
  let y = x * 2
  let z = y + 1
  z
```

### Multi-clause (pattern matching on arguments)

```cure
fn factorial(n: Int) -> Int
  | 0 -> 1
  | n -> n * factorial(n - 1)
```

### Guards

```cure
fn abs(x: Int) -> Int when x >= 0 = x

fn classify(x: Int) -> String
  | x when x > 0 -> "positive"
  | x when x < 0 -> "negative"
  | _ -> "zero"
```

### FFI (Foreign Function Interface)

`@extern(<module>, <function>, <arity>)` binds a Cure function to an external
BEAM function. It is a **type-only signature**: the compiler trusts the declared
types and lowers each call to a direct remote call.

```cure
@extern(:erlang, :abs, 1)
fn abs(x: Int) -> Int
```

Two rules are enforced:

- The head must be **fully typed** -- every parameter annotated and a return type
  declared (`E056`). An untyped head would default to `Any` and defeat the type
  checker.
- The declaration must **not have a body** (`E057`). Codegen ignores any body,
  so a `= ...` is dead code.

Erlang/OTP modules are plain atoms (`:erlang`, `:io`); Elixir modules use their
dotted `Elixir.` path (`Elixir.Cure.FSM.Builtins`). `@extern` composes with
`local` for private bindings.

See `docs/FFI.md` for the full guide (module forms, effects, lowering, and
patterns).

## Types

### Primitive types

`Int`, `Float`, `String`, `Bool`, `Atom`, `Char`, `Pid`, `Pid(Inbox)`
(v0.25.0), `Ref` (v0.25.0).

`Pid` alone elaborates to `{:pid, :any}`, the top of the covariant `Pid`
family; `Pid(Inbox)` attaches an inbox protocol (an ADT or record
type) against which the Melquiades Operator type-checks every send.
`Ref` is the monitor reference returned by `Std.Process.monitor/1`.

### Composite types

- `List(T)` -- linked list
- `Map(K, V)` -- hash map
- `%[A, B]` -- tuple
- `A -> B` -- function type

### ADT (sum types)

```cure
type Option(T) = Some(T) | None
type Result(T, E) = Ok(T) | Error(E)
```

**Multi-line layout (v0.21.0).** ADT declarations may span multiple
lines with leading `|` on continuation lines. The single-line and
multi-line forms are syntactically equivalent.

```cure
type Shape =
  | Circle(Int)
  | Square(Int)
  | Triangle(Int, Int, Int)
```

**Function-type payloads (v0.21.0).** Constructor payloads accept
arbitrary type expressions, including function arrows:

```cure
type Callback = On(Int -> Int) | Off
type Transform = Morph((Int, Int) -> Int) | Id
```

Function-typed payloads compile to first-class functions at runtime;
pattern matching binds the function to a variable you can call like
any other lambda.

### Refinement types

```cure
type NonZero = {x: Int | x != 0}
type Positive = {x: Int | x > 0}
type Percentage = {p: Int | p >= 0 and p <= 100}
```

Refinement type subtyping is verified at compile time using Z3.
With **path-sensitive refinement** (v0.17.0), the type of a variable
appearing in an `if`/`match` guard is refined for the duration of that
branch.

### Sigma types (dependent pairs)

```cure
type Sized(T) = Sigma(n: Nat, Vector(T, n))
```

A Sigma type pairs a value with a type that may depend on it.
The surface forms `Sigma(T1, T2)`, `Sigma(name: T1, T2)`, and
`DPair(...)` are all recognised.

### Pi types (dependent function types)

```cure
fn append(xs: Vector(T, m), ys: Vector(T, n)) -> Vector(T, m + n)
```

Return types may freely reference parameter names. The type checker
substitutes the call-site arguments and normalises the resulting
expression with `Cure.Types.Reduce` before comparing.

### Equality types

```cure
refl(x) : Eq(T, x, x)
```

`Eq(T, a, b)` is the type of proofs that `a == b` at type `T`.
`refl(x)` is the only constructor; `rewrite eq in expr` is the only
eliminator. All Eq values are erased at runtime.

### Implicit arguments

```cure
fn id({T}, x: T) -> T = x
```

Parameters in `{...}` braces are inferred from explicit-argument types
at each call site via `Cure.Types.Unify`. They cost nothing at runtime.

### Holes

```cure
fn safe_head(xs: List(T)) -> T = ?body
```

A `?name` or `??` placeholder triggers a `:hole_goal` pipeline event
that reports the goal type and the local context at the hole position.

### Totality

```cure
@total true
fn factorial(n: Int) -> Int
  | 0 -> 1
  | n -> n * factorial(n - 1)
```

`Cure.Types.Totality` classifies every function as `:total`,
`:partial`, or `:unknown`. Add `@total true` to upgrade the
classification to a compile-time error.

## Records

Records are named, typed product types. They compile to BEAM maps with a
`__struct__` discriminator key, giving them nominal identity at runtime.

### Definition

```cure
rec Point
  x: Int
  y: Int

rec Person
  name: String
  age: Int

rec Rectangle
  origin: Point
  width: Int
  height: Int
```

Type parameters are supported for generic records:

```cure
rec Pair(A, B)
  first: A
  second: B
```

Type parameters are erased at runtime but are tracked by the type checker.

### Construction

Use `TypeName{field: expr, ...}` to build a record value:

```cure
fn make_point(x: Int, y: Int) -> Point = Point{x: x, y: y}
fn origin() -> Point = Point{x: 0, y: 0}
fn make_person(name: String, age: Int) -> Person =
  Person{name: name, age: age}
```

### Field access

Use dot notation `record.field`, which compiles to `maps:get(field, map)`:

```cure
fn x_coord(p: Point) -> Int = p.x
fn area(r: Rectangle) -> Int = r.width * r.height
fn rect_origin_x(r: Rectangle) -> Int = r.origin.x  # nested access
```

### Record update

Produce a modified copy of a record with `TypeName{base | field: val, ...}`.
Only the listed fields change; all others are copied from `base`:

```cure
fn set_x(p: Point, new_x: Int) -> Point = Point{p | x: new_x}
fn birthday(p: Person) -> Person = Person{p | age: p.age + 1}
fn translate(p: Point, dx: Int, dy: Int) -> Point =
  Point{p | x: p.x + dx, y: p.y + dy}
fn rename(p: Person, new_name: String) -> Person =
  Person{p | name: new_name}
```

Multiple fields can be overridden in one expression:

```cure
fn move(p: Point, nx: Int, ny: Int) -> Point = Point{p | x: nx, y: ny}
```

The type name before `{` is required and must match the type of the base
expression. The compiler verifies override field types against the declared
schema.

### Runtime representation

Records compile to BEAM maps:

```
Point{x: 3, y: 4}  ->  %{__struct__: :point, x: 3, y: 4}
```

Record construction uses `map_field_assoc` (`:=>`). Record update uses
`map_field_exact` (`:=`) which requires the keys to already exist, giving
a `bad_key` error at runtime if the base value has an incompatible shape.

## Protocols

```cure
proto Show(T)
  fn show(x: T) -> String

impl Show for Int
  fn show(x: Int) -> String = Std.String.from_int(x)
```

Protocol dispatch is compiled to guard-based multi-clause functions.

## FSMs (Finite State Machines)

Cure supports two FSM compilation modes:

**Simple mode** (no `on_transition` block) compiles to a `gen_statem`
module. The resulting machine carries a freeform data term that each
transition's `do` action may replace.

```cure
fsm TrafficLight
  Red    --timer-->     Green
  Green  --timer-->     Yellow
  Yellow --timer-->     Red
  *      --emergency--> Red
```

**Callback mode** (v0.22.0, triggered by the presence of an
`on_transition` block) compiles to a `GenServer` whose state is a
fixed `%Cure.FSM.State{}` struct with three fields:

- `:caller` -- the pid that spawned the FSM. Outbound notifications
  (`Std.Fsm.notify/1`, `@notify_transitions`) reach this pid. Defaults
  to the spawning process when `Std.Fsm.spawn/1` is used.
- `:meta` -- FSM-private bookkeeping, invisible to callers.
- `:payload` -- user-visible domain value; read by
  `Std.Fsm.get_state/1`.

Every lifecycle hook receives the struct as its last argument and may
return either a full `%Cure.FSM.State{}`, a partial map with
`:payload`/`:meta` keys that is merged into the current struct, or
any bare value which is interpreted as the new payload.

```cure
fsm Counter
  @notify_transitions

  Idle --inc--> Idle
  Idle --reset--> Idle

  on_transition
    (:idle, :inc,   _evp, %{payload: n, meta: m}) ->
      %[:ok, :idle, %{payload: n + 1, meta: m}]
    (:idle, :reset, _evp, %{payload: _, meta: m}) ->
      %[:ok, :idle, %{payload: 0, meta: m}]
    (_, _, _, state) -> %[:ok, :__same__, state]

  on_start
    (state) ->
      notify(:started)
      %[:ok, state]
```

### Lifecycle hooks

- `on_start` -- called inside `init/1`. Receives the struct. May
  return `:ok`, `{:ok, state}`, or `{:ok, partial}`.
- `on_stop` -- called from `terminate/2`. Receives `(reason, state)`.
- `on_transition` -- called on every accepted event. Receives
  `(current_state, event, event_payload, %FsmState{})`.
- `on_enter` -- called on entering a state. Receives
  `(state, %FsmState{})`.
- `on_exit` -- called on leaving a state. Receives
  `(state, %FsmState{})`.
- `on_failure` -- called when a transition is disallowed or the
  handler returns `{:error, reason}`. Receives
  `(event, event_payload, %FsmState{})`.
- `on_timer` -- called every `@timer` milliseconds. Receives
  `(state, %FsmState{})`.

### Annotations

- `@timer N` -- drive `on_timer` every `N` ms.
- `@terminal State` -- mark a state as terminal (no outgoing
  transitions required for deadlock freedom).
- `@invariant expr` / `@verify expr` -- reserved for the verifier.
- `@initial :state_name` -- override the initial state (default: the
  first non-wildcard source).
- `@notify_transitions` -- after every successful transition, send
  `{:cure_fsm, pid, {:transition, from, event, to, payload}}` to the
  caller.
- `@auto_caller` -- when `:caller` is not explicitly provided, fall
  back to the spawning process recorded under
  `:cure_fsm_spawner` in the FSM's process dictionary.

### Events with payloads

Events may carry an arbitrary payload, threaded through to
`on_transition` as the third argument:

```cure
let pid = Std.Fsm.spawn(:"Cure.FSM.Counter")
Std.Fsm.send_with(pid, :inc, %{source: :button})
```

### Notifying the outside world

Inside any lifecycle hook body, `notify(message)` sends `message` to
the FSM's `:caller`. Callable as a bare identifier in Cure source; at
the Elixir level it resolves to `Cure.FSM.State.notify_self/1`. When
called outside a running FSM process, `notify/1` is a no-op returning
`:no_caller`.

The compiler verifies reachability, deadlock freedom, hard-event
exclusivity, and terminal-state validity at compile time.

## Actors and Supervisors (v0.25.0)

Typed supervision trees live in two container shapes and a typed send
operator. See `docs/SUPERVISION.md` for the authoritative reference.

### The Melquiades Operator `<-|` / `✉`

`pid <-| message` sends `message` to `pid` and returns the message. The
unicode envelope `✉` is an interchangeable alias. Both forms lower to
Erlang's `!` operator; non-blocking, never raises for a dead receiver.
The keyword form `send target, msg` is preserved and desugars to the
same `{:send, ...}` MetaAST node. Binding power is one notch below `|>`,
non-associative.

```cure
pid <-| :ping
pid ✉  :ping
request
|> encode()
|> worker_pid <-| _
```

### `actor` containers

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

- `with <expr>` seeds the initial payload.
- `on_start`, `on_message`, `on_stop` reuse the FSM callback-clause
  grammar (pattern tuple, optional `when` guard, body).
- Inside any clause body, `notify(message)` sends to the spawning
  caller (resolved via the process dictionary).
- The clause return value is the new payload; returning a full
  `%Cure.Actor.State{}` struct replaces the whole runtime state.
- Compiles to a loaded `GenServer` module named `Cure.Actor.<Name>`.
- Spawned and managed by `Cure.Actor.Runtime` (ETS-backed registry,
  automatic cleanup on `DOWN`); also reachable from Cure through
  `Std.Actor`.

### `sup` containers

```cure
sup App.Root
  strategy  = :one_for_one
  intensity = 3
  period    = 5
  children
    Counter       as counter
    Counter       as counter_b (restart: :transient)
    App.External  as external  (restart: :permanent, shutdown: 10000)
    sup Workers   as workers
```

- `strategy` defaults to `:one_for_one` (also accepts `:one_for_all`,
  `:rest_for_one`, `:simple_one_for_one`).
- `intensity` defaults to `3`; `period` defaults to `5`.
- `children` lists one child spec per line. Each line is
  `Module as child_id` with an optional parenthesised keyword list of
  `restart: ...`, `shutdown: ...`.
- Child module resolution: dotted paths verbatim; bare names resolve
  to `Cure.Actor.<Name>` (worker default) or `Cure.Sup.<Name>`
  (with the soft-keyword prefix `sup <Name> as id`).
- Compile-time verification rejects unknown strategies, invalid
  `restart`/`shutdown` values, non-positive `period`, duplicate child
  ids, and trivial self-reference cycles (codes `E047`/`E048`/`E050`).
- Compiles to a `Supervisor`-behaviour module named `Cure.Sup.<Name>`;
  managed from Cure via `Std.Supervisor`.

### Links, monitors, trap_exit

`Std.Process` exposes the raw BEAM process primitives (`link/1`,
`unlink/1`, `monitor/1` returning a `Ref`, `demonitor/1`,
`trap_exit/1`, `exit/2`, `self/0`, `is_alive/1`). Most calls map
directly to `:erlang` BIFs; `monitor/1` and `trap_exit/1` route
through thin wrappers in `Cure.Process.Builtins` so the Cure
signatures stay idiomatic.

### Typed sends

The type checker has a dedicated clause for `{:send, ...}` that
unifies the message type against the receiver's declared inbox and
emits `E046 Inbox Mismatch` on conflict. Bare `Pid` elaborates to
`{:pid, :any}` so existing FFI code remains compatible.

## Applications (v0.26.0)

The `app` container wraps an entire supervision tree into a first-class
OTP application. See `docs/APP.md` for the authoritative reference.

```cure
app MyApp
  vsn          = "0.1.0"
  description  = "My humble application"
  root         = sup MyApp.Root
  applications = [:logger, :crypto]
  env          = %{port: 4000}
  on_start
    (start_kind, args) -> do_start(start_kind, args)
  on_stop
    (state) -> cleanup(state)
  on_phase :warm_cache
    (_args, _kind, _start_args) -> Std.Cache.warm()
```

- `vsn`, `description`, `root`, `applications`, `included_applications`,
  `env`, and `registered` are top-level assignments inside the `app`
  body. They override the corresponding values in the
  `[application]` table of `Cure.toml` (with `applications` merged
  instead of replaced).
- `on_start` / `on_stop` reuse the actor / FSM callback-clause grammar
  and produce the generated module's `start/2` and `stop/1` bodies.
- Each `on_phase :name` block introduces one 3-argument clause
  `(phase_args, start_kind, start_args)` feeding the generated
  `start_phase/3` callback. Phase names must agree with
  `[application].start_phases` in `Cure.toml` (code `E053`).
- `root = ...` accepts four forms: `sup Name`, `Name`,
  `App.Sub.Root`, and an atom literal (`:my_app_sup`). The first two
  resolve to `:"Cure.Sup.<Name>"`; dotted paths and atoms are used
  verbatim. A phase-only app may omit `root` entirely. Unresolved
  roots surface as `E054`.
- The container compiles to `:"Cure.App.<Name>"` (a loaded
  `Application`-behaviour module). With `--output-dir`, the bytecode
  and an OTP `<name>.app` resource file are persisted alongside every
  other Cure module.
- `Cure.Project.compile_project/2` enforces at most one `app`
  container per project and cross-checks its name against
  `[application].name` (code `E051`).

`cure release` (also `mix cure.release`) packages the compiled
application as a bootable BEAM release under
`_build/cure/rel/<name>/`; failure modes surface as `E052` (missing
`app`) or `E055` (release-build failure). From Cure source,
`Std.App` offers `ensure_all_started`, `start`, `stop`, `get_env`,
`put_env`, `which_applications`, `loaded_applications`, and
`start_phase` as thin wrappers over `:application`.

## Pattern Matching
The `match` construct is specified normatively at version 1.0.0 in
[`docs/MATCH.md`](MATCH.md), which covers grammar, the full pattern
sub-grammar, static / dynamic / operational semantics, formatter
conformance, the Maranget-style exhaustiveness algorithm, refinement
narrowing, the diagnostic catalogue, and a soundness proof sketch.
This section is an informal overview; for any conflict, `MATCH.md`
is the authority.

`match` (and `let`) support deep destructuring across every structural
form in the language. As of v0.18.0 the supported pattern shapes are:
### Literals and variables
```cure
match x
  0      -> "zero"
  n      -> "nonzero"
  _      -> "never reached"
```
`_` is the wildcard. A name starting with `_` (for example `_unused`)
is a binding that silences the unused-variable warning.
### Tuples and lists
```cure
match pair
  %[a, b]        -> a + b
  %[a, b, _rest] -> a + b

match xs
  []             -> "empty"
  [h | t]        -> "non-empty"
  [a, b, c]      -> "exactly three"
```
Cons is single-head only: `[h | t]` binds `h` to the head and `t` to
the tail. Matching against a literal-length list (`[a, b, c]`) requires
the list to have that exact length.
### Maps
```cure
match request
  %{method: "GET", path: p}    -> fetch(p)
  %{method: m, path: _}        -> reject(m)
```
Map keys in pattern position must be literal values. A map pattern
matches if every listed key is present in the subject; keys not
mentioned are ignored (open matching, like Elixir's `%{...}`).
### Records and field punning
```cure
match person
  Person{name, age}                    -> salute(name, age)
  Person{name, address: Address{city}} -> greet(name, city)
```
A bare identifier inside a record pattern is shorthand for
`name: name` (field punning). Record patterns compile to map patterns
with a `__struct__ := :tag` guard, so they only match values built
with the same record type.
### ADT constructors
```cure
match result
  Ok(v)         -> v
  Error(reason) -> default

match option
  Some(x) -> x
  None()  -> 0
```
Nullary constructors must be written with empty parentheses
(`None()`), never bare `None` -- a bare `None` is a fresh variable
binding.
### The pin operator `^x`
```cure
let target = get_tag()

match event.tag
  ^target -> :hit
  _       -> :miss
```
`^x` compares against a previously-bound value rather than binding
fresh. Lowered by the compiler to a guard `V_fresh =:= V_x`.
### Repeated variables
```cure
match pair
  %[x, x] -> :equal
  _       -> :different
```
A name that appears twice in the same pattern binds on its first
occurrence and is turned into an equality guard at every later
position (so the pattern only matches when all occurrences hold the
same value).
### Nested destructuring
Any combination of the above can be nested:
```cure
match value
  %[_, %{list: [head | tail]}, _] -> handle(head, tail)
  Person{name: n, address: Address{city: c, zip: _}} when c == "Madrid" ->
    greet(n)
```
### Exhaustiveness
The compiler checks pattern exhaustiveness. Shallow coverage gaps are
reported by the flat classifier (`E004`); nested gaps (tuples of ADTs,
records in tuples, etc.) are reported with a concrete witness under
code `E025`.

## Conditional Dispatch (`pickup`)

Cure has no `if` / `elif` / `else` chain. Predicate dispatch goes
through the `pickup` construct, specified normatively at version
1.0.0 in [`docs/PICKUP.md`](PICKUP.md). The mental model is one
sentence: *`pickup` walks the clauses and picks up the first one
whose guard is true.* Each block lists boolean guards in source
order and terminates in a mandatory `else -> e` clause that makes
the construct total by construction. Guards must type to `Bool`
(no truthy / falsy coercion); evaluation short-circuits at the
first `true`. The legacy `if`/`elif` shape is removed; the
`cure rewrite if-to-pickup` tool migrates surviving sources.

```cure
pickup
  status >= 500 -> :server_error
  status >= 400 -> :client_error
  status >= 300 -> :redirect
  status >= 200 -> :ok
  else          -> :informational
```

For the full diagnostic catalogue, formatter rules, refinement
context-strengthening, tail-position guarantee, and migration story,
see `docs/PICKUP.md`.

## Control Flow

### If/else

Legacy `if`/`else` is removed; see
[`docs/PICKUP.md`](PICKUP.md) for the canonical replacement. The
shape historically rendered as `if x > 0 then "positive" else
"non-positive"` is now written:

```cure
pickup
  x > 0 -> "positive"
  else  -> "non-positive"
```

### Let bindings

```cure
let x = 42
let y = x * 2
```

**In-place destructuring (v0.21.0).** `let` bindings support the same
pattern grammar as `match` arms: ADT constructors, tuples, cons
cells, record field punning, maps, and binary segments. Each bound
variable carries the narrowed scrutinee type.

```cure
let Ok(x)         = parse(input)       # ADT constructor
let %[a, b]       = pair                # tuple destructure
let [h | _rest]   = xs                  # cons destructure
let Point{x, y}   = p                   # record punning
let <<b, _::binary>> = buf              # binary destructure
```

Non-exhaustive `let` patterns emit code `E034` as a warning (not an
error): the binding still compiles, and Erlang's `=` raises at
runtime on a failed match. Setting `partial: true` on the assignment
metadata suppresses the warning.

### Binary patterns

Binary literals use Erlang-style segment grammar between `<<` and
`>>`. Every segment is `value [:: specifier_chain]`; the specifier
chain is hyphen-joined and covers type (`integer`, `float`, `utf8`,
`utf16`, `utf32`, `binary`, `bytes`, `bitstring`, `bits`),
signedness, endianness, `size(expr)`, and `unit(n)`. See
`docs/BINARIES.md` for the authoritative reference.

```cure
let header       = <<42, 1, 2, 3>>
let <<tag, _::binary>> = buffer

match frame
  <<len::16, payload::binary-size(len), _::binary>> -> payload
  <<>>                                              -> <<>>
```

Binary exhaustiveness is tracked via code `E031`.

**Trailing `rest::binary` refinement (v0.22.0).** A trailing
`rest::binary` (or `rest::bytes`, `rest::bitstring`) segment after
byte-aligned preceding segments inherits a refinement of the form
`byte_size(rest) == byte_size(scrutinee) - sum_of_preceding_sizes`.
The refinement flows through the SMT translator, so subsequent
binary matches on `rest` type-check without having to re-assert the
length invariant. Non-byte-aligned or non-linearisable preceding
segments degrade the refinement to plain `Bitstring` and emit the
`:refinement_ignored` event under code `E037`.

### Binary comprehension generators

```cure
[byte for <<byte <- "abc">>]       # [97, 98, 99]
[word for <<word::16 <- buf>>]     # 16-bit words, big-endian
[ch   for <<ch::utf8 <- text>>]    # UTF-8 code points
```

A binary comprehension generator (v0.22.0) wraps the whole generator
in `<<...>>`: pattern segments, the `<-` arrow, and the source
expression all live between `<<` and `>>`. The segments reuse the
regular binary-pattern grammar (specifier chains, `::size(n)`,
`::unit(k)`, `::utf8`, ...). The comprehension body sees the
generator variables narrowed to their segment types. A non-bitstring
source produces an `E036` warning.

### Lambda block bodies

Anonymous functions (`fn (params) -> body`) accept four body shapes:

```cure
# Single expression (v0.12.0+).
fn (x) -> x + 1

# Indented block (v0.19.0+). Only usable where the lexer emits
# `:indent`/`:dedent`, i.e. at top level or inside block-forming
# constructs.
fn (x) ->
  let y = x + 1
  y * 2

# Brace-delimited (v0.22.0). Statements separated by `;`; the final
# expression is the body's result. Works anywhere, including inside
# argument lists where newlines are suppressed.
map(xs, fn (x) -> { let y = x + 1; y * 2 })

# end-terminated (v0.22.0). A single `end` keyword closes the body.
# Statement separator is `;` (or newline when newlines are emitted).
map(xs, fn (x) -> let y = x + 1; y * 2; end)
```

All four shapes produce the same `{:block, meta, exprs}` AST node.
The `:block_shape` meta key (`:brace` or `:end`) lets the algebra
formatter round-trip the author's chosen form. `end` is a reserved
keyword from v0.22.0.

An unclosed brace or missing `end` surfaces as `E035 Lambda Block
Unterminated`.

### Pipe operator

```cure
5 |> double |> add(1)
# desugars to: add(double(5), 1)
```
