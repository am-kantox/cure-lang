# Cure Standard Library Reference

The standard library is self-hosted -- written in Cure itself under `lib/std/`.
Compile with `mix cure.compile_stdlib` or `cure stdlib`.

## Std.Core (36 functions)

Identity, composition, and utility:
- `identity(x)` -- return x unchanged
- `compose(f, g)` -- function composition (f . g)
- `pipe(x, f)` -- apply f to x
- `apply(f, x)` -- apply f to x
- `const(x)` -- return a function that always returns x

Boolean operations:
- `bool_not(x)`, `bool_and(x, y)`, `bool_or(x, y)`, `bool_xor(x, y)`

Comparison:
- `eq(x, y)`, `ne(x, y)`, `lt(x, y)`, `le(x, y)`, `gt(x, y)`, `ge(x, y)`
- `min(x, y)`, `max(x, y)`, `clamp(value, lo, hi)`

Result type (`Ok(value)` / `Error(reason)`):
- `ok(v)`, `error(e)`, `is_ok(r)`, `is_error(r)`
- `unwrap_ok(r, default)`, `unwrap_error(r, default)`
- `map_ok(r, f)`, `map_error(r, f)`, `and_then(r, f)`, `or_else(r, f)`

Option type (`Some(value)` / `None()`):
- `some(v)`, `none()`, `is_some(o)`, `is_none(o)`
- `unwrap(o, default)`, `map_option(o, f)`, `flat_map_option(o, f)`, `option_or(o, default)`

## Std.List (25 functions)

Queries: `length(l)`, `is_empty(l)`

Access: `head(l, default)`, `tail(l)`, `last(l, default)`, `nth(l, idx, default)`

Construction: `cons(elem, l)`, `append(a, b)`, `concat(lists)`, `reverse(l)`

Transformations: `map(l, f)`, `filter(l, pred)`, `foldl(l, acc, f)`, `foldr(l, acc, f)`, `flat_map(l, f)`, `zip_with(a, b, f)`

Slicing: `take(l, n)`, `drop(l, n)`

Search: `contains(l, elem)`, `find(l, pred, default)`, `any(l, pred)`, `all(l, pred)`

Aggregation: `sum(l)`, `product(l)`, `count(l, pred)`

## Std.Math (18 functions)

FFI: `abs(x)`, `sqrt(x)`, `pow(base, exp)`, `log(x)`, `log2(x)`, `log10(x)`, `ceil(x)`, `floor(x)`, `round(x)`, `pi()`

Pure: `max(a, b)`, `min(a, b)`, `clamp(v, lo, hi)`, `sign(x)`, `negate(x)`, `is_even(x)`, `is_odd(x)`, `safe_div(a, b)`

## Std.String (17 functions)

`length(s)`, `is_empty(s)`, `concat(a, b)`, `downcase(s)`, `upcase(s)`, `trim(s)`, `trim_leading(s)`, `trim_trailing(s)`, `from_int(n)`, `from_float(f)`, `from_atom(a)`, `to_int(s)`, `to_float(s)`, `to_atom(s)`, `split(s, sep)`, `repeat(s, n)`, `reverse(s)`

## Std.Pair (9 functions)

`element(idx, tuple)`, `first(pair)`, `second(pair)`, `swap(pair)`, `map_first(pair, f)`, `map_second(pair, f)`, `map_both(pair, f, g)`, `to_list(pair)`, `from_list(list)`

## Std.Access (protocol + lenses)

Key-based access to data structures, modelled on Elixir's
[`Access`](https://hexdocs.pm/elixir/Access.html) behaviour. Implements the
protocol for plain maps (records compile to maps, so records are covered
automatically) and for keyword-style lists of `%[key, value]` pairs.

Protocol:

- `fetch(container, key) -> Option(Any)`
- `get_and_update(container, key, f) -> Tuple` where `f` receives
  `Some(value)` or `None()` and returns either `%[got, new_value]` or the
  atom `:pop`.
- `pop(container, key) -> Tuple` returns `%[popped_or_nil, new_container]`.
  On a map that carries a `:__struct__` discriminator (i.e. a record) this
  raises `:struct_pop_not_allowed`, matching Elixir's struct semantics.

Direct helpers:

- `fetch(c, k)`, `fetch_bang(c, k)` (raises `:key_error` on miss),
  `get(c, k, default)`, `get_and_update(c, k, f)`, `pop(c, k)`.

Accessor (lens) ADT and factories for use with `get_in`/`put_in`/...:

- `key(k)` -- plain key; missing keys collapse to `nil` in `get_in`.
- `key_default(k, default)` -- key with a fallback substituted on miss.
- `key_bang(k)` -- required key; raises `:key_error` on miss.
- `elem_at(i)` -- 0-based tuple element accessor.
- `at(i)` -- 0-based list index accessor.
- `all()` -- traverse every element of a list.
- `filter(pred)` -- traverse every element of a list satisfying `pred`.

Nested traversal (all accept a `List(Accessor)`):

- `fetch_in(c, keys)` -- `Option(Any)`; `None()` on any missing step.
- `get_in(c, keys)` -- returns `nil` on any missing step.
- `put_in(c, keys, value)` -- replace the leaf value.
- `update_in(c, keys, f)` -- apply `f` to the leaf.
- `get_and_update_in(c, keys, f)` -- the full workhorse; `f` returns
  `%[got, new_leaf]` or `:pop`.
- `pop_in(c, keys)` -- remove the leaf, returning `%[popped, rebuilt]`.

Example -- upcase every language name in a nested structure:

```cure
let data = %{
  langs: [
    %{name: "elixir"},
    %{name: "cure"}
  ]
}

update_in(data, [key(:langs), all(), key(:name)], fn(n) -> Std.String.upcase(n))
## => %{langs: [%{name: "ELIXIR"}, %{name: "CURE"}]}
```

## Std.Io (8 functions)

`put_chars(text)`, `println(text)`, `print(text)`, `int_to_string(n)`, `float_to_string(f)`, `atom_to_string(a)`, `print_int(n)`, `print_float(f)`

## Std.Show (protocol)

Protocol: `show(x) -> String`

Implementations: Int, Float, String, Bool, Atom

Convenience: `show_line(x)` -- show with trailing newline

## Std.System (10 functions)

`monotonic_time()`, `system_time(unit)`, `timestamp_ms()`, `timestamp_us()`, `self()`, `node()`, `system_info(key)`, `otp_version()`, `cpu_count()`, `exit(code)`

## Std.Fsm (12 functions)

`spawn(module)`, `spawn_named(module, name)`, `stop(pid)`, `send(pid, event)`, `send_batch(pid, events)`, `get_state(pid)`, `state(pid)`, `is_alive(pid)`, `info(pid)`, `history(pid)`, `lookup(name)`

## Std.Equal (4 functions)

Propositional equality combinators (all erased at runtime).

- `refl(x)` -- reflexivity: `Eq(T, x, x)`.
- `sym(eq)` -- symmetry: `Eq(T, a, b) -> Eq(T, b, a)`.
- `trans(p, q)` -- transitivity: `Eq(T, a, b), Eq(T, b, c) -> Eq(T, a, c)`.
- `cong(f, eq)` -- congruence: `Eq(T, a, b) -> Eq(U, f(a), f(b))`.

All values produced are the runtime atom `:cure_refl`.

## Std.Refine

A collection of common refinement-type aliases plus their
corresponding runtime predicates.

Type aliases:

- `NonZero`, `Positive`, `Negative`, `NonNegative`, `NonPositive`,
  `Percentage`, `PositiveFloat`, `Probability`.

Predicates:

- `positive?(n)`, `non_negative?(n)`, `percentage?(p)`,
  `probability?(p)`.

## Std.Actor (8 functions, v0.25.0)

Runtime-facing surface for typed actor modules compiled from `actor`
containers. Every function delegates to `Cure.Actor.Builtins`, which in
turn calls `Cure.Actor.Runtime`.

- `spawn(actor_module)` -- start an actor; the spawning process is
  recorded as its `:caller`.
- `spawn_with_payload(actor_module, payload)` -- start with an explicit
  initial payload.
- `spawn_named(actor_module, name)` -- spawn and register under a
  string name for later lookup.
- `stop(pid)` -- stop a running actor.
- `send(pid, message)` -- cast semantics; counterpart of `pid <-| msg`.
- `get_state(pid)` -- return the actor's current user-visible payload.
- `is_alive(pid)` -- whether the actor process is alive.
- `lookup(name)` -- look up a named actor, returning its pid.

## Std.Process (9 functions, v0.25.0)

Raw BEAM process primitives. Most entries map directly to `:erlang`
BIFs via `@extern`; `monitor/1` and `trap_exit/1` route through thin
wrappers in `Cure.Process.Builtins` so the Cure signatures can stay
idiomatic.

- `link(pid)`, `unlink(pid)` -- toggle bidirectional process linking.
- `monitor(pid) -> Ref` -- install a process monitor; the caller will
  later receive `{:DOWN, ref, :process, pid, reason}` on termination.
- `demonitor(ref)` -- remove a previously installed monitor.
- `trap_exit(flag) -> Bool` -- toggle `trap_exit` on the caller,
  returning the previous value.
- `exit(pid, reason)` -- send an exit signal.
- `self()` -- return the caller's own pid.
- `is_alive(pid)` -- whether the pid is alive on this node.

## Std.Supervisor (7 functions, v0.25.0)

Start, stop, and introspect Cure supervisor trees compiled from `sup`
containers. Each `sup Name` container compiles to a loaded BEAM module
at `Cure.Sup.<Name>`; these functions delegate to `Cure.Sup.Builtins`,
which wraps `Cure.Sup.Runtime`.

- `start(sup_module)` -- start a supervisor tree and return its pid.
- `start_with(sup_module, init)` -- start with an explicit initial
  argument threaded into the tree's `init/1`.
- `stop(sup_module)` -- stop a running tree.
- `which_children(sup_module)` -- return the supervisor's direct
  children as `%[id, child_pid, type, modules]` tuples.
- `count_children(sup_module)` -- return a map of `%{type => count}`.
- `lookup(sup_module)` -- return the pid of a running tree or `nil`.
- `list()` -- return the list of currently-running supervisor module
  atoms.

## Std.App (9 functions, v0.26.0)

Cure-facing surface for the OTP application lifecycle. Each Cure
`app` container compiles to a loaded `:"Cure.App.<Name>"` module that
implements the `:application` behaviour (`start/2`, `stop/1`, and,
when `on_phase :name` clauses are present, `start_phase/3`). This
module delegates to `Cure.App.Builtins`, which wraps the Erlang
`:application` BIFs and returns plain atoms / values instead of the
OTP `{:ok, _}` tuples.

- `ensure_all_started(name)` -- start the application and every
  dependency in its closure. Returns `:ok` whether or not the
  application was already running.
- `start(name)` -- start an already-loaded application; idempotent.
- `stop(name)` -- stop a running application; idempotent.
- `get_env(name, key)` -- read an application-env value; `nil` when
  unset.
- `get_env(name, key, default)` -- read an application-env value
  with a user-supplied fallback.
- `put_env(name, key, value)` -- write an application-env value.
- `which_applications()` -- return `[%[name, description, vsn], ...]`
  tuples for every running application.
- `loaded_applications()` -- return the list of loaded application
  name atoms.
- `start_phase(name, phase, phase_args)` -- manually invoke a
  start-phase callback. Normally the OTP boot script calls this
  while the release boots; the entry exists for tests and scripted
  scenarios.

Example -- boot the app and read its `port` env:

```cure
use Std.App

fn boot() -> Atom = Std.App.ensure_all_started(:my_app)
fn port() -> Int  = Std.App.get_env(:my_app, :port, 4000)
```

## Std.Time (v0.27.0)

Time primitives on top of OTP's `Calendar` / `DateTime`:

- `now()`, `utc_now()` -- wall-clock reader returning an
  `Instant{micros: Int}` record. Both carry `! Io`.
- `parse_iso8601(s)` -- `Result(Instant, ParseError)`; accepts
  canonical `YYYY-MM-DDTHH:MM:SSZ` or `+HH:MM` offsets with
  optional fractional seconds.
- `format_iso8601(i)` -- render an `Instant` back to a UTC string,
  suppressing `.000000` when the microsecond part is zero.
- `add(i, d)`, `diff(a, b)` -- arithmetic on `Instant` and
  `Duration` records.
- `zone(i, name)` -- project into a named zone (`"UTC"`,
  `"+02:00"`, `"-05:00"`); returns `Result(String, ParseError)`.
- `to_unix(i)`, `of_unix(s)` -- Unix-second conversions.
- `millis(n)`, `seconds(n)`, `minutes(n)`, `hours(n)` -- smart
  constructors for `Duration`.

Runtime bridge: `:cure_std_time`.

## Std.Regex (v0.27.0)

Thin wrapper over OTP's `:re`:

- `compile(pattern)` -- `Result(Regex, RegexError)` where `Regex`
  is an opaque record.
- `compile_bang(pattern)` -- raises `ArgumentError` on invalid
  patterns.
- `is_match(r, input) -> Bool`.
- `run(r, input) -> Option(Matched)` -- `Matched{whole, groups}`
  with the first non-whole capture list.
- `scan(r, input) -> List(Matched)` -- every match in source
  order.
- `replace(r, input, replacement)` -- `String`; backreferences
  (`\1`, `\2`, ...) supported in `replacement`.
- `split(r, input) -> List(String)`.

Invalid patterns surface through the new `E060 Regex Invalid`
error code.

## Std.CRDT (v0.27.0)

Five state-based CvRDTs whose `merge/2` operations are
commutative, associative, and idempotent (enforced by the
test suite in `test/cure/stdlib/cure_std_crdt_test.exs`):

- **`GCounter`**: grow-only counter. `g_empty`, `g_increment`,
  `g_value`, `g_merge`.
- **`PNCounter`**: positive/negative counter. `pn_empty`,
  `pn_increment`, `pn_decrement`, `pn_value`, `pn_merge`.
- **`ORSet`**: observed-remove set. `or_empty`, `or_add`,
  `or_remove`, `or_value`, `or_merge`.
- **`LWWRegister`**: last-write-wins register. `lww_empty`,
  `lww_set`, `lww_value`, `lww_merge`.
- **`MVRegister`**: multi-value register keeping the latest write
  per node. `mv_empty`, `mv_write`, `mv_values`, `mv_merge`.

Every CRDT is a tagged map under the `__struct__` key; the runtime
bridge is `:cure_std_crdt`.
