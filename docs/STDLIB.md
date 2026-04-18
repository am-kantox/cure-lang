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
