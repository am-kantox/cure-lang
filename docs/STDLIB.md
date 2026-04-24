# Cure Standard Library Reference

The standard library is self-hosted: every module below is written in Cure
itself under `lib/std/` and compiled by `mix cure.compile_stdlib` (or
`cure stdlib`). Each compiled module produces a loadable `:"Std.<Name>"`
BEAM module; external calls use `@extern(:module, :fun, arity)` to punch
through to `:erlang`, OTP, or the dedicated `Cure.*.Builtins` helpers in
`lib/cure/stdlib/`.

## Viewing the stdlib

- **On the web** -- [cure-lang.org/stdlib](https://cure-lang.org/stdlib) renders every `Std.*` module from the same `.cure` sources, grouped by topic. A single module page lives at `/stdlib/<Module>` with a GitHub "View source" link and anchored entries for every public function / type / protocol.
- **Locally** -- `cure doc` produces the same layout under `_build/cure/doc/`. The tree is self-contained (HTML + one CSS + one JS file) so the output can be zipped up or served from any static host. See [`docs/DOC.md`](DOC.md) for the configuration reference.
- **In the REPL** -- `:doc Std.List.map` pulls the `##` comments and renders them as ANSI using `Cure.REPL.Markdown`.

Since v0.29.0, every module below carries a module-level `## Examples`
block in its source doc comments, and four high-traffic `Std.Core`
functions (`compose`, `map_ok`, `and_then`, `map_option`) also carry
per-function examples. Every example round-trips through
`mix cure.compile_stdlib` without modification.

The documentation below is organised by topic:

- [Core utilities](#core-utilities)  -- `Std.Core`, `Std.Io`, `Std.Show`,
  `Std.System`, `Std.Test`.
- [Containers and data](#containers-and-data)  -- `Std.List`, `Std.Map`,
  `Std.Set`, `Std.Vector`, `Std.Pair`, `Std.Option`, `Std.Result`,
  `Std.Match`, `Std.Access`.
- [Protocols](#protocols)  -- `Std.Eq`, `Std.Ord`, `Std.Functor`.
- [Value-shaped modules](#value-shaped-modules)  -- `Std.String`,
  `Std.Math`, `Std.Regex`, `Std.Json`, `Std.Http`, `Std.Time`.
- [Types and proofs](#types-and-proofs)  -- `Std.Refine`, `Std.Equal`,
  `Std.Proof`.
- [Concurrency and OTP](#concurrency-and-otp)  -- `Std.Actor`,
  `Std.Fsm`, `Std.Process`, `Std.Supervisor`, `Std.App`.
- [Lazy evaluation and randomness](#lazy-evaluation-and-randomness)  --
  `Std.Iter`, `Std.Gen`.
- [Replicated data types](#replicated-data-types)  -- `Std.CRDT`.

All source line references point at `lib/std/<module>.cure`.

## Module groups and selective preload

Every stdlib module carries a single nullary declaration near the top
of its source that assigns it to a group:

```cure path=null start=null
fn __group__() -> Atom = :collections
```

`Cure.Stdlib.Preload` scans `lib/std/*.cure` at Elixir compile time
(tracked via `@external_resource`), builds a static
`%{module => group}` map, and exposes it through
`Cure.Stdlib.Preload.module_groups/0`. The REPL, host applications,
and test fixtures can then ask for a subset of the library via
`Cure.Stdlib.Preload.stdlib_modules/1` or the identically-named
`:kind` option on `Cure.Stdlib.Preload.preload/1`:

- `:none` (the default everywhere) -- nothing is loaded.
- `:all` -- every stdlib module is preloaded, matching the historical
  behaviour of the CLI entry points (`cure run`, `cure compile`,
  `mix cure.check.examples`).
- a single group atom, or a list of them -- the union of the matching
  modules is loaded.

Known groups and their current membership (also the source of truth
for `Cure.Stdlib.Preload.known_groups/0`):

- `:core` -- `Std.Core`, `Std.Equal`, `Std.Eq`, `Std.Ord`, `Std.Show`,
  `Std.Functor`, `Std.Refine`, `Std.Proof`. `Std.Proof` is the one
  module that relies on the compile-time default (`:core`); `proof`
  containers only admit `Eq(...)` returns, so no explicit
  `__group__/0` lives in its source.
- `:collections` -- `Std.List`, `Std.Map`, `Std.Set`, `Std.Vector`,
  `Std.Pair`, `Std.Match`, `Std.Access`, `Std.Iter`.
- `:text` -- `Std.String`, `Std.Regex`, `Std.Json`.
- `:numeric` -- `Std.Math`.
- `:system` -- `Std.Io`, `Std.System`, `Std.Time`, `Std.App`,
  `Std.CRDT`.
- `:concurrency` -- `Std.Actor`, `Std.Fsm`, `Std.Process`,
  `Std.Supervisor`.
- `:option` -- `Std.Option`, `Std.Result`.
- `:test` -- `Std.Test`, `Std.Gen`.
- `:network` -- `Std.Http`.

The REPL reads a `.cure.repl.toml` file at startup (project-local
wins over the home-wide fallback) and threads the resolved kind
through `Cure.Stdlib.Preload.preload/1` and
`Cure.REPL.Docs.default_uses/1`. See `docs/REPL.md` for the TOML
shape and worked examples.

## Core utilities
### Std.Core
Identity, composition, boolean operations, comparison, and both the
`Result` and `Option` sum types. These are the most commonly used
combinators in Cure programs.
#### Combinators
- `identity(x: T) -> T`  -- returns `x` unchanged.
- `compose(f: B -> C, g: A -> B) -> (A -> C)`  -- right-to-left
  composition; `compose(f, g)(x) == f(g(x))`.
- `pipe(x: T, f: T -> U) -> U`  -- flip of `apply`; reads left-to-right.
- `apply(f: T -> U, x: T) -> U`  -- function application as a value.
- `const(x: T) -> (U -> T)`  -- constant function factory.
#### Boolean operations
- `bool_not(x: Bool) -> Bool`
- `bool_and(x: Bool, y: Bool) -> Bool`
- `bool_or(x: Bool, y: Bool) -> Bool`
- `bool_xor(x: Bool, y: Bool) -> Bool`
#### Comparison
- `eq(x, y) -> Bool`, `ne(x, y) -> Bool`  -- equality and inequality.
- `lt`, `le`, `gt`, `ge`  -- strict and non-strict comparison.
- `min(x, y) -> T`, `max(x, y) -> T`  -- pointwise extrema.
- `clamp(value: T, lo: T, hi: T) -> T`  -- clamp into `[lo, hi]`.
#### Result type
`Result(T, E)` lowers to `Ok(v) == {:ok, v}` and
`Error(e) == {:error, e}`.
- `ok(v) -> Result(T, E)`, `error(e) -> Result(T, E)`  -- constructors.
- `is_ok(r) -> Bool`, `is_error(r) -> Bool`  -- predicates.
- `unwrap_ok(r, default) -> T`, `unwrap_error(r, default) -> E`  --
  total extractors.
- `map_ok(r, f) -> Result(U, E)`, `map_error(r, f) -> Result(T, F)`
  -- functorial mapping over each arm.
- `and_then(r, f) -> Result(U, E)`  -- monadic bind over `Ok`.
- `or_else(r, f) -> Result(T, F)`  -- monadic bind over `Error`.
#### Option type
`Option(T)` lowers to `Some(v) == {:some, v}` and `None() == {:none}`.
- `some(v)`, `none()`  -- constructors.
- `is_some(o) -> Bool`, `is_none(o) -> Bool`  -- predicates.
- `unwrap(o, default) -> T`  -- total extractor.
- `map_option(o, f) -> Option(U)`  -- functorial map.
- `flat_map_option(o, f) -> Option(U)`  -- monadic bind.
- `option_or(o, default) -> T`  -- unwrap-or-default alias used by
  `Std.Match`.
### Std.Io
Minimal stdout surface. Every impure entry carries the `! Io` effect in
its signature so callers are forced to declare the effect.
- `put_chars(text: String) -> Atom ! Io`  -- write without newline;
  wraps `:io.put_chars/1`.
- `println(text: String) -> Atom ! Io`  -- write `text <> "\n"`.
- `print(text: String) -> Atom ! Io`  -- alias for `put_chars`.
- `int_to_string(n: Int) -> String`,
  `float_to_string(f: Float) -> String`,
  `atom_to_string(a: Atom) -> String`  -- cheap conversion helpers.
- `print_int(n: Int) -> Atom`, `print_float(f: Float) -> Atom`  --
  convenience wrappers that call `println` on the converted value.
### Std.Show
A single-method display protocol. Instances convert a value to its
human-readable `String` form; this is the counterpart to Elixir's
`String.Chars` / `Inspect` split.
- `proto Show(T)` with `fn show(x: T) -> String`.
- Built-in impls for `Int`, `Float`, `String`, `Bool`, `Atom`.
  Strings are wrapped in quotes, atoms are prefixed with `:`.
- `show_line(x: T) -> String`  -- `show(x) <> "\n"`.
### Std.System
Time, process-identity, and VM introspection primitives. `exit/1` maps
to `:erlang.halt/1` and terminates the whole BEAM node.
- `monotonic_time() -> Int`  -- native monotonic time units.
- `system_time(unit: Atom) -> Int`  -- OS system time in `unit`.
- `timestamp_ms() -> Int`, `timestamp_us() -> Int`  -- fixed-unit
  convenience readers.
- `self() -> Pid`  -- caller's pid.
- `node() -> Atom`  -- local node name atom.
- `system_info(key: Atom) -> T`  -- raw `:erlang.system_info/1`.
- `otp_version() -> T`  -- value of `:otp_release` as an Erlang
  charlist.
- `cpu_count() -> Int`  -- number of logical processors.
- `exit(code: Int) -> Atom`  -- halt the node with status `code`.
### Std.Test
Assertion primitives plus a shrinking-aware property runner.
- `assert(cond: Bool) -> Atom`  -- raises `:assertion_failed` on
  `false`.
- `assert_eq(a, b) -> Atom`  -- raises `:not_equal`.
- `assert_ne(a, b) -> Atom`  -- raises `:unexpectedly_equal`.
- `assert_gt(a, b) -> Atom`, `assert_lt(a, b) -> Atom`  -- strict
  ordering assertions.
- `forall(gen, property, runs) -> Atom`  -- run `property` against
  `runs` samples drawn from `gen`. Returns `:ok` on success; raises
  `:property_failed` on a counterexample.
- `forall_default(gen, property) -> Atom`  -- wrapper with 100 runs.
- `forall_shrunk(gen, property, runs) -> T`  -- like `forall/3` but
  shrinks the first failing sample via `Std.Gen.shrink/1` before
  raising `:property_failed_with_shrunk`.
- `forall_shrunk_default(gen, property) -> T`  -- 100-run default.

## Containers and data
### Std.List
Eager, persistent, singly-linked lists. All operations are recursive
over cons cells.
#### Queries
- `length(l: List(T)) -> Int`  -- `@extern :erlang.length/1`.
- `is_empty(l) -> Bool`
#### Access
- `head(l, default) -> T`, `tail(l) -> List(T)`  -- safe head/tail.
- `last(l, default) -> T`  -- tail-recursive last element.
- `nth(l, idx, default) -> T`  -- 0-based random access.
#### Construction
- `cons(elem, l) -> List(T)`, `append(a, b) -> List(T)`,
  `concat(lists) -> List(T)`, `reverse(l) -> List(T)`  -- the last
  uses a private tail-recursive accumulator.
#### Transformations
- `map(l, f)`, `filter(l, pred)`  -- classic list comprehensions.
- `foldl(l, acc, f)`, `foldr(l, acc, f)`  -- `f` is curried
  (`elem -> acc -> acc`).
- `flat_map(l, f)`, `zip_with(a, b, f)`.
#### Slicing
- `take(l, n) -> List(T)`, `drop(l, n) -> List(T)`.
#### Search
- `contains(l, elem) -> Bool`, `find(l, pred, default) -> T`,
  `any(l, pred) -> Bool`, `all(l, pred) -> Bool`.
#### Destructuring helpers (v0.18.0)
- `uncons(l) -> Tuple`  -- returns `%[head, tail]`, empty list maps to
  `%[[], []]`.
- `split_first(l, default) -> Tuple`  -- like `uncons`, but falls back
  to `default` for an empty list.
#### Aggregation
- `sum(l: List(Int)) -> Int`, `product(l: List(Int)) -> Int`.
- `count(l, pred) -> Int`  -- number of elements that match `pred`.
### Std.Map
Thin wrapper around Erlang's `:maps` module plus one Cure-level helper.
- `new() -> Map`, `put(key, value, map) -> Map`,
  `get(key, map) -> V`, `remove(key, map) -> Map`  -- the workhorse
  setters and getters.
- `get_or(key, map, default) -> V`  -- default-aware accessor.
- `has_key(key, map) -> Bool`, `size(map) -> Int`,
  `is_empty(map) -> Bool`, `count(map) -> Int`  -- predicates and
  cardinality.
- `keys(map)`, `values(map)`, `to_list(map)`,
  `from_list(list)`  -- enumeration helpers.
- `merge(map1, map2) -> Map`  -- right-biased merge.
### Std.Set
Sets are encoded as maps whose values are all `true`. Every operation
delegates to `Std.Map`, keeping the implementation trivial.
- `new() -> Map`, `add(elem, set) -> Map`, `remove(elem, set) -> Map`.
- `member(elem, set) -> Bool`, `size(set) -> Int`, `is_empty(set) -> Bool`.
- `to_list(set) -> List(T)`, `from_list(list) -> Map`.
- `union(a, b) -> Map`, `intersection(a, b) -> Map`,
  `difference(a, b) -> Map`.
### Std.Vector
Dynamic arrays with an explicit length field, backed by a list.
Representation: `%[:vector, len, list]`.
- `empty()`, `singleton(x)`, `from_list(list)`, `to_list(vec)`.
- `length(vec) -> Int`, `is_empty(vec) -> Bool`.
- `cons(x, vec) -> Tuple`, `head(vec) -> T`, `tail(vec) -> Tuple`.
- `append(a, b) -> Tuple`, `map(vec, f) -> Tuple`.
The length is tracked at the type level so dependent type checks can
reason about vector sizes.
### Std.Pair
Two-tuple helpers. Internally delegates to `:erlang.element/2`.
- `element(index: Int, tuple) -> T`  -- 1-based BEAM accessor; also
  used by `Std.Vector`.
- `first(pair) -> T`, `second(pair) -> T`, `swap(pair) -> Tuple`.
- `map_first(pair, f)`, `map_second(pair, f)`, `map_both(pair, f, g)`.
- `to_list(pair) -> List(T)`, `from_list(list) -> Tuple`  -- the
  `from_list` helper pads or truncates pathological inputs with
  zeros.
### Std.Option
Standalone `Option(T)` module (parallel to the Option helpers in
`Std.Core`; kept separate so it can be imported alone).
- `some(value)`, `none()`  -- constructors.
- `is_some(o)`, `is_none(o)`  -- predicates.
- `unwrap(o, default) -> T`, `or_else(o, default) -> T`  -- total
  extractors.
- `map(o, f) -> Option(U)`, `flat_map(o, f) -> Option(U)`  -- functor
  and monad.
- `filter(o, pred) -> Option(T)`  -- drops the value when `pred`
  returns `false`.
- `zip(a, b) -> Option(Tuple)`  -- `Some(%[va, vb])` when both sides
  are `Some`, else `None()`.
### Std.Result
Standalone `Result(T, E)` module. Same shape as the Result half of
`Std.Core`, with one extra combinator:
- `ok(v)`, `error(e)`, `is_ok(r)`, `is_error(r)`, `unwrap(r, default)`,
  `unwrap_error(r, default)`  -- basics.
- `map(r, f) -> Result(U, E)`, `map_error(r, f) -> Result(T, F)`.
- `and_then(r, f) -> Result(U, E)`, `or_else(r, f) -> Result(T, F)`.
- `flatten(r: Result(Result(T, E), E)) -> Result(T, E)`  -- monadic
  join.
### Std.Match
Convenience helpers built on top of v0.18.0 deep destructuring. Every
function here is implemented with nested patterns and serves as a
smoke test for the pattern engine.
#### Pair / Tuple
- `unpack_pair(t) -> Tuple`  -- identity for a pair, pass-through
  otherwise.
- `fst(t) -> T`, `snd(t) -> T`  -- first and second element with
  graceful fall-through.
#### Lists
- `head_tail(l, default) -> Tuple`, `uncons(l) -> Tuple`,
  `first_two(l, default) -> Tuple`.
#### Options / Results
- `unwrap_ok(r, default) -> T`, `unwrap_some(o, default) -> T`.
### Std.Access
Key-based access to containers and composable lenses, modelled on
Elixir's [`Access`](https://hexdocs.pm/elixir/Access.html) behaviour.
The module has four layers.
#### Protocol
```cure path=null start=null
proto Access(C)
  fn fetch(container: C, key: Any) -> Option(Any)
  fn get_and_update(container: C, key: Any,
                    f: Option(Any) -> Any) -> Tuple
  fn pop(container: C, key: Any) -> Tuple
```
Implementations ship for:
- `Map`  -- covers Cure records, which compile to maps with a
  `__struct__` discriminator. `pop/2` on such a record raises
  `:struct_pop_not_allowed`, matching Elixir's struct semantics.
- `List` used keyword-style, i.e. a list of `%[key, value]` pairs.

`get_and_update` callbacks must return either `%[got, new_value]` or
the atom `:pop`; `pop/2` returns `%[popped_or_nil, new_container]`.
#### Direct helpers
- `fetch(c, k) -> Option(Any)`.
- `fetch_bang(c, k) -> Any`  -- raises `:key_error` on miss.
- `get(c, k, default) -> Any`.
- `get_and_update(c, k, f) -> Tuple`, `pop(c, k) -> Tuple`.
#### Accessor ADT and factories
`Accessor` values are plain ADT constructors; they compose into
`List(Accessor)` paths that `get_in`, `put_in`, and friends walk.
- `key(k)`  -- plain key accessor; missing keys collapse to `nil`.
- `key_default(k, default)`  -- substitutes `default` on miss.
- `key_bang(k)`  -- required key; raises `:key_error` on miss.
- `elem_at(i)`  -- 0-based tuple element accessor (translated to
  BEAM's 1-based `element/2`).
- `at(i)`  -- 0-based list index accessor.
- `all()`  -- traverses every element of a list.
- `filter(pred)`  -- traverses list elements that satisfy `pred`.
#### Nested traversal
All of the following accept `List(Accessor)`:
- `fetch_in(c, keys) -> Option(Any)`  -- `None()` on any miss.
- `get_in(c, keys) -> Any`  -- `nil` on any miss.
- `put_in(c, keys, value)`  -- replace the leaf.
- `update_in(c, keys, f)`  -- apply `f` to the leaf.
- `get_and_update_in(c, keys, f)`  -- the full workhorse; `f`
  receives the leaf and returns `%[got, new_leaf]` or `:pop`.
- `pop_in(c, keys) -> Tuple`  -- remove the leaf, returning
  `%[popped, rebuilt]`.
#### Example
```cure path=null start=null
let data = %{
  langs: [
    %{name: "elixir"},
    %{name: "cure"}
  ]
}

update_in(data, [key(:langs), all(), key(:name)],
  fn(n) -> Std.String.upcase(n))
## => %{langs: [%{name: "ELIXIR"}, %{name: "CURE"}]}
```

## Protocols
### Std.Eq
Structural equality with a default `ne/2`.
- `proto Eq(T)` with `fn eq(a: T, b: T) -> Bool`.
- Built-in impls for `Int`, `Float`, `String`, `Bool`, `Atom`.
- `ne(a, b) -> Bool`  -- `!eq(a, b)`.
### Std.Ord
Three-way comparison plus total-order helpers.
- `proto Ord(T)` with `fn compare(a: T, b: T) -> Atom` returning
  `:lt`, `:eq`, or `:gt`.
- Built-in impls for `Int`, `Float`, `String`, `Atom`.
- `lt`, `le`, `gt`, `ge`  -- derived from `compare/2`.
### Std.Functor
Minimal `fmap`-style functor. Useful as a teaching example of the
protocol system.
- `proto Functor(F)` with `fn fmap(container: F, f: A -> B) -> F`.
- `impl Functor for List` delegates to `Std.List.map/2`.

## Value-shaped modules
### Std.String
Binaries in Erlang are Cure's `String`. Length is measured in bytes;
case conversion and trimming delegate to OTP's `:string` module, which
is Unicode-aware.
- `length(s) -> Int`  -- byte size.
- `is_empty(s) -> Bool`, `concat(a, b) -> String`  -- uses the `<>`
  operator.
- `downcase(s)`, `upcase(s)`  -- Unicode case conversion.
- `trim(s)`, `trim_leading(s)`, `trim_trailing(s)`  -- whitespace
  trimming.
- `from_int(n)`, `from_float(f)`, `from_atom(a)`  -- conversions to
  binary.
- `to_int(s)`, `to_float(s)`, `to_atom(s)`  -- parsing primitives
  (raise on bad input, as per the underlying BIFs).
- `split(s, sep) -> List(String)`  -- `:binary.split/2`.
- `repeat(s, n) -> String`  -- `:binary.copy/2`.
- `reverse(s) -> String`  -- byte-level reversal via an intermediate
  charlist (not grapheme-aware).
### Std.Math
Integer helpers written in Cure plus `@extern` wrappers around the
`:math` module.
- FFI: `abs(x)`, `sqrt(x)`, `pow(base, exp)`, `log(x)`, `log2(x)`,
  `log10(x)`, `ceil(x)`, `floor(x)`, `round(x)`, `pi()`.
- Pure Cure: `max(a, b)`, `min(a, b)`, `clamp(v, lo, hi)`, `sign(x)`,
  `negate(x)`, `is_even(x)`, `is_odd(x)`, `safe_div(a, b)` (returns
  `0` when the divisor is zero).
### Std.Regex (v0.27.0)
Thin wrapper over OTP's `:re`. The `@regex "..."` compile-time
decorator (recognised by `Cure.Stdlib.CompileAssert`) hoists pattern
validation into the compiler, surfacing invalid patterns as
`E060 Regex Invalid` at build time instead of runtime.
- `rec Regex { handle: T }`  -- opaque compiled handle.
- `rec Matched { whole: String, groups: List(String) }`  -- capture
  result; `groups` holds the numbered captures after the whole match.
- `type RegexError = InvalidPattern(String) | NotMatched`.
- `compile(pattern) -> Result(Regex, RegexError)`.
- `compile_bang(pattern) -> Regex`  -- raises on invalid patterns;
  prefer `compile/1` in library code.
- `is_match(r, input) -> Bool`.
- `run(r, input) -> Option(Matched)`.
- `scan(r, input) -> List(Matched)`.
- `replace(r, input, replacement) -> String`  -- supports `\1`, `\2`,
  ... backreferences inside `replacement`.
- `split(r, input) -> List(String)`.

Runtime module: `:cure_std_regex`.
### Std.Json (v0.23.0)
Typed JSON encoder/decoder that pairs with the v0.21.0
`@derive(JSON)` extension.
- `rec JsonPair { key: String, value: Value }`.
- `type Value = Null | Bool(Bool) | Num(Float) | Str(String)
   | Arr(List(Value)) | Obj(List(JsonPair))`  -- numbers are always
  floats at runtime.
- `encode(v: Value) -> String`, `decode(src: String) -> Result(Value, String)`.
- `num_of_int(n: Int) -> Value`  -- widen an integer to the JSON
  number path.
- `pair(k: String, v: Value) -> JsonPair`  -- construction helper for
  `Obj(...)`.

Runtime module: `:cure_std_json`.
### Std.Http (v0.23.0)
Minimal HTTP/1.1 client built on OTP's `:httpc`, with no external
dependencies. Uses `Result` so HTTP calls compose naturally with the
rest of the standard library.
- `rec Response { status: Int, headers: List((String, String)),
   body: Bitstring }`.
- `type HttpError = Timeout | BadStatus(Int) | NetworkError(String)
   | DecodeError(String)`.
- `get(url) -> Result(Response, HttpError)`.
- `get_with_headers(url, headers) -> Result(Response, HttpError)`.
- `post(url, headers, body) -> Result(Response, HttpError)`.
- `head(url) -> Result(Response, HttpError)`.

Runtime module: `:cure_std_http`.
### Std.Time (v0.27.0)
Instants and durations on top of OTP's `Calendar` / `DateTime`.
Everything is stored in microseconds so arithmetic stays monomorphic.
- `rec Instant { micros: Int }`  -- Unix-microsecond timestamp.
- `rec Duration { micros: Int }`  -- signed length.
- `type ParseError = InvalidFormat(String) | OutOfRange(String)`.
#### Wall clock (effectful)
- `now() -> Instant ! Io`, `utc_now() -> Instant ! Io`.
#### ISO 8601
- `parse_iso8601(s) -> Result(Instant, ParseError)`  -- accepts
  `Z`, `+HH:MM`, `-HH:MM` offsets and fractional seconds up to
  microseconds.
- `format_iso8601(i: Instant) -> String`  -- renders UTC with a `Z`
  suffix, suppressing `.000000` when zero.
#### Arithmetic
- `add(i: Instant, d: Duration) -> Instant`.
- `diff(a: Instant, b: Instant) -> Duration`.
- `zone(i: Instant, name: String) -> Result(String, ParseError)`  --
  project into `"UTC"`, `"+02:00"`, or any `"+/-HH:MM"` form.
#### Unix conversions
- `to_unix(i) -> Int`  -- Unix seconds, truncated toward zero.
- `of_unix(s: Int) -> Instant`  -- Unix seconds into an Instant at
  second granularity.
#### Duration constructors
- `millis(n)`, `seconds(n)`, `minutes(n)`, `hours(n) -> Duration`.

Runtime module: `:cure_std_time`.

## Types and proofs
### Std.Refine
Refinement type aliases plus matching runtime predicates. The aliases
carry predicate obligations; the predicates are plain totals you can
call at runtime.
#### Type aliases
- `NonZero = {x: Int | x != 0}`
- `Positive = {x: Int | x > 0}`
- `Negative = {x: Int | x < 0}`
- `NonNegative = {x: Int | x >= 0}`
- `NonPositive = {x: Int | x <= 0}`
- `Percentage = {p: Int | p >= 0 and p <= 100}`
- `PositiveFloat = {x: Float | x > 0.0}`
- `Probability = {p: Float | p >= 0.0 and p <= 1.0}`
#### Predicates
- `positive?(n: Int) -> Bool`, `non_negative?(n: Int) -> Bool`.
- `percentage?(p: Int) -> Bool`, `probability?(p: Float) -> Bool`.
### Std.Equal
Propositional equality combinators. All four values reduce to the
runtime atom `:cure_refl`; the types are meaningful only to the type
checker, so these helpers are erased at runtime.
- `refl(x: T) -> Eq(T, x, x)`  -- reflexivity.
- `sym(eq: Eq(T, a, b)) -> Eq(T, b, a)`  -- symmetry.
- `trans(p, q) -> Eq(T, a, c)`  -- transitivity.
- `cong(f: T -> U, eq: Eq(T, a, b)) -> Eq(U, f(a), f(b))`  --
  congruence.
### Std.Proof
A `proof`-container (declared with `proof Std.Proof`) holding
laws-as-programs. Like `Std.Equal`, every definition returns
`:cure_refl` at runtime; the value is meaningful only at type-check
time.
#### Arithmetic
- `plus_zero(n: Int) -> Eq(Int, n, n)`.
- `zero_plus(n: Int) -> Eq(Int, n, n)`.
- `plus_comm(a: Int, b: Int) -> Eq(Int, a, a)`  -- commutativity
  witness (the statement is reduced by the checker).
#### List laws
- `append_nil(xs: List(T)) -> Eq(List(T), xs, xs)`.
- `map_id(xs: List(T)) -> Eq(List(T), xs, xs)`.

## Concurrency and OTP
### Std.Actor (v0.25.0)
Runtime-facing surface for typed actor modules compiled from `actor`
containers. Every function delegates to `Cure.Actor.Builtins`, which
in turn calls `Cure.Actor.Runtime`.
- `spawn(actor_module) -> Pid`  -- start an actor; the caller is
  recorded as its `:caller`.
- `spawn_with_payload(actor_module, payload) -> Pid`.
- `spawn_named(actor_module, name) -> Pid`  -- spawn and register
  under a string name.
- `stop(pid) -> Atom`  -- terminate the actor.
- `send(pid, message) -> Any`  -- cast semantics; counterpart of the
  Melquiades `<-|` operator (both lower to Erlang's `!`).
- `get_state(pid) -> Any`  -- read the actor's user-visible payload.
- `is_alive(pid) -> Bool`.
- `lookup(name: String) -> Pid`  -- reverse lookup by registered
  name.
### Std.Fsm
Runtime surface for FSM modules compiled from `fsm` containers. All
entries delegate to `Cure.FSM.Builtins`, which wraps
`Cure.FSM.Runtime`.
#### Lifecycle
- `spawn(fsm_module) -> Pid`  -- start an instance; caller is the
  recorded `:caller`.
- `spawn_with_payload(fsm_module, payload) -> Pid`.
- `spawn_with(fsm_module, init) -> Pid`  -- accepts a
  `%Cure.FSM.State{}`, a keyword list, or a plain map containing
  `:caller`, `:meta`, and `:payload`.
- `spawn_named(fsm_module, name) -> Pid`, `stop(pid) -> Atom`.
#### Events
- `send(pid, event) -> Atom`  -- deliver an event without payload.
- `send_with(pid, event, payload) -> Atom`  -- deliver an event
  carrying a payload.
- `send_batch(pid, events) -> Atom`  -- deliver a list of events.
#### Introspection
- `get_state(pid) -> Tuple`  -- `%[state, payload]`.
- `full_state(pid) -> Tuple`  -- `%[state, %FsmState{...}]`.
- `state(pid) -> Atom`  -- current state atom.
- `is_alive(pid) -> Bool`, `info(pid) -> Map`,
  `history(pid) -> List(Atom)`.
- `lookup(name: String) -> Pid`.
#### Lifecycle-hook helpers
- `notify(message) -> Atom`  -- send `message` back to the FSM's
  registered caller. A no-op returning `:no_caller` outside an FSM
  process.
- `caller(pid) -> Pid`  -- return the caller pid registered for a
  running FSM, or `nil`.
### Std.Process (v0.25.0)
Raw BEAM process primitives. Most entries are direct `@extern`
wrappers around `:erlang` BIFs; `monitor/1` and `trap_exit/1` route
through thin wrappers in `Cure.Process.Builtins` so the Cure
signatures can stay idiomatic.
- `link(pid) -> Atom`, `unlink(pid) -> Atom`  -- toggle bidirectional
  linking.
- `monitor(pid) -> Ref`  -- returns the new `Ref` primitive;
  subsequent `{:DOWN, ref, :process, pid, reason}` messages arrive
  on termination.
- `demonitor(ref: Ref) -> Bool`.
- `trap_exit(flag: Bool) -> Bool`  -- toggles `trap_exit` on the
  caller, returning the previous value.
- `exit(pid, reason: Atom) -> Atom`.
- `self() -> Pid`, `is_alive(pid) -> Bool`.
### Std.Supervisor (v0.25.0)
Start, stop, and introspect Cure supervisor trees compiled from `sup`
containers. Each `sup Name` compiles to a loaded `Cure.Sup.<Name>`
module.
- `start(sup_module) -> Pid`, `start_with(sup_module, init) -> Pid`
  -- the latter threads `init` into the tree's `init/1`.
- `stop(sup_module) -> Atom`.
- `which_children(sup_module) -> List(Tuple)`  -- returns
  `%[id, child_pid, type, modules]` tuples.
- `count_children(sup_module) -> Map`  -- `%{type => count}`.
- `lookup(sup_module) -> Pid`  -- pid or `nil`.
- `list() -> List(Atom)`  -- every tracked supervisor module.
### Std.App (v0.26.0)
Cure-facing surface for the OTP application lifecycle. Each `app`
container compiles to a loaded `Cure.App.<Name>` module implementing
the `:application` behaviour (`start/2`, `stop/1`, and when
`on_phase :name` clauses are present, `start_phase/3`). The helpers
below wrap the Erlang `:application` BIFs via `Cure.App.Builtins`,
returning plain atoms / values instead of OTP's `{:ok, _}` tuples.
- `ensure_all_started(name) -> Atom`  -- start the application and
  every transitive dependency.
- `start(name) -> Atom`, `stop(name) -> Atom`  -- both idempotent.
- `get_env(name, key) -> Any`, `get_env(name, key, default) -> Any`
  -- read env values; the two-arity form returns `nil` when unset.
- `put_env(name, key, value) -> Atom`.
- `which_applications() -> List(Tuple)`  -- `[%[name, description,
  vsn], ...]` for every running application.
- `loaded_applications() -> List(Atom)`.
- `start_phase(name, phase, phase_args) -> Atom`  -- manually invoke
  a `on_phase` callback (normally driven by the boot script; exposed
  for tests).

Example:
```cure path=null start=null
use Std.App

fn boot() -> Atom = Std.App.ensure_all_started(:my_app)
fn port() -> Int  = Std.App.get_env(:my_app, :port, 4000)
```

## Lazy evaluation and randomness
### Std.Iter (v0.19.0)
Minimal lazy iterators. Comprehensions in Cure are eager today (they
lower to `:lists.map`), so this module ships a hand-rolled shape plus
two of the most common consumers so programs can stop early without
materialising the tail.

An iterator is a zero-argument lambda returning either
`Some(%[element, next_iter])` or `None()` -- close to Elixir's
`Stream` shape.
#### Constructors
- `empty()`  -- iterator that is immediately exhausted.
- `from_list(list) -> Atom -> Any`  -- walks a list left-to-right.
- `range(lo, hi) -> Atom -> Any`  -- inclusive integer range.
#### Consumers
- `fold(it, acc, f) -> T`  -- left fold; `f` is curried
  (`elem -> acc -> acc`).
- `take(it, n) -> List(Any)`  -- take at most `n` elements.
- `to_list(it) -> List(Any)`  -- eagerly materialise; guard infinite
  iterators with `take/2`.
### Std.Gen (v0.19.0)
Tiny stateless generator API used by `Std.Test`. Generators are
zero-argument lambdas returning a fresh value on every call;
randomness is delegated to `:rand`.
#### Primitives
- `seed(alg, seed) -> Tuple`  -- delegate to `:rand.seed/2`.
#### Scalar generators
- `int_in(lo, hi) -> Int`  -- uniform integer in `[lo, hi]`.
- `bool() -> Bool`  -- fair coin.
- `constant(v) -> T`  -- always returns `v`.
#### Combinators
- `one_of(list, default) -> Int`  -- pick an element from a
  non-empty list (falls back to `default` for an empty input).
- `list_of_int(n, lo, hi) -> List(Int)`  -- length-`n` list of
  uniform integers.
- `list_int(max_len, lo, hi) -> List(Int)`  -- list of random length
  up to `max_len`.
#### Shrinking (v0.23.0)
- `shrink_int(v: Int) -> List(Int)`  -- candidate smaller ints,
  aggressive shrinks first.
- `shrink_list(xs: List(Int)) -> List(List(Int))`  -- shorter lists
  first.
- `shrink(v: T) -> List(T)`  -- polymorphic dispatch; returns `[]`
  for types without a defined shrink.

Runtime module: `:cure_std_gen`.

## Replicated data types
### Std.CRDT (v0.27.0)
Five state-based CvRDTs whose `merge/2` operations satisfy three
laws (enforced by `test/cure/stdlib/cure_std_crdt_test.exs`):
```text path=null start=null
merge(a, b) == merge(b, a)                       (commutative)
merge(a, merge(b, c)) == merge(merge(a, b), c)   (associative)
merge(a, a) == a                                 (idempotent)
```
All CRDTs are tagged maps under a `__struct__` key and carry a
`node_id` to tag mutations so merges can reconcile conflicting
updates deterministically. Runtime module: `:cure_std_crdt`.
### GCounter
Grow-only counter. Per-replica counts are summed on read.
- `g_empty() -> GCounter`.
- `g_increment(c, node: Atom, by: Int) -> GCounter`.
- `g_value(c) -> Int`.
- `g_merge(a, b) -> GCounter`.
### PNCounter
Positive/negative counter; internally two `GCounter`s. `value`
returns `sum(p) - sum(n)`.
- `pn_empty() -> PNCounter`.
- `pn_increment(c, node, by) -> PNCounter`.
- `pn_decrement(c, node, by) -> PNCounter`.
- `pn_value(c) -> Int`, `pn_merge(a, b) -> PNCounter`.
### ORSet
Observed-remove set. Each addition carries a unique tag; removals
drop exactly the tags the remover has observed.
- `or_empty() -> ORSet`.
- `or_add(s, node: Atom, elem: T) -> ORSet`.
- `or_remove(s, elem: T) -> ORSet`.
- `or_value(s) -> List(T)`, `or_merge(a, b) -> ORSet`.
### LWWRegister
Last-write-wins register. Merges pick the side with the higher
timestamp; ties break on node id.
- `lww_empty(node: Atom) -> LWWRegister`.
- `lww_set(r, value: T, stamp: Int, node: Atom) -> LWWRegister`.
- `lww_value(r) -> T`, `lww_merge(a, b) -> LWWRegister`.
### MVRegister
Multi-value register that retains every concurrent write so the
caller can resolve the conflict manually.
- `mv_empty() -> MVRegister`.
- `mv_write(r, value, stamp, node) -> MVRegister`.
- `mv_values(r) -> List(T)`, `mv_merge(a, b) -> MVRegister`.
