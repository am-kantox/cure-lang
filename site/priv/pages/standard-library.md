%{
  title: "Standard Library",
  description: "Self-hosted stdlib written in Cure itself: 24 modules, ~260 functions.",
  order: 6
}
---

The standard library is self-hosted -- written in Cure under `lib/std/`.
Compile it with `mix cure.compile_stdlib` or `cure stdlib`. The output goes
to `_build/cure/ebin/` as regular `.beam` files callable from Erlang or Elixir.

24 modules. ~260 functions. No Elixir runtime dependency beyond FFI calls
to `:erlang`, `:math`, `:maps`, `:lists`, `:string`, `:binary`, `:io`, `:rand`,
and `:os`.

v0.19.0 additions: `Std.Proof` (propositional laws), `Std.Gen` (generators
for property-based testing), `Std.Iter` (lazy iterator protocol). `Std.Test`
gains `forall/3` and `forall_default/2`.

All modules are documented with `##` doc comments. Run `cure doc lib/std/`
to generate browsable HTML documentation.

## Std.Core

36 functions. Identity, composition, boolean logic, comparison, Result and
Option operations. This is the foundation everything else builds on.

### Identity and composition

```cure
fn identity(x: T) -> T = x

fn compose(f: B -> C, g: A -> B) -> (A -> C) =
  fn(x) -> f(g(x))

fn pipe(x: T, f: T -> U) -> U = f(x)

fn apply(f: T -> U, x: T) -> U = f(x)

fn const(x: T) -> (U -> T) =
  fn(y) -> x
```

### Boolean operations

```cure
fn bool_not(x: Bool) -> Bool = if x then false else true
fn bool_and(x: Bool, y: Bool) -> Bool = if x then y else false
fn bool_or(x: Bool, y: Bool) -> Bool = if x then true else y
fn bool_xor(x: Bool, y: Bool) -> Bool = if x then bool_not(y) else y
```

### Comparison

```cure
fn eq(x: T, y: T) -> Bool = x == y
fn ne(x: T, y: T) -> Bool = x != y
fn lt(x: T, y: T) -> Bool = x < y
fn le(x: T, y: T) -> Bool = x <= y
fn gt(x: T, y: T) -> Bool = x > y
fn ge(x: T, y: T) -> Bool = x >= y
fn min(x: T, y: T) -> T = if x <= y then x else y
fn max(x: T, y: T) -> T = if x >= y then x else y
fn clamp(value: T, lo: T, hi: T) -> T =
  if value < lo then lo else if value > hi then hi else value
```

### Result operations

Result is represented as `Ok(value) -> {:ok, value}` and
`Error(reason) -> {:error, reason}`:

```cure
fn ok(value: T) -> Result(T, E) = Ok(value)
fn error(reason: E) -> Result(T, E) = Error(reason)
fn is_ok(result: Result(T, E)) -> Bool
fn is_error(result: Result(T, E)) -> Bool
fn unwrap_ok(result: Result(T, E), default: T) -> T
fn unwrap_error(result: Result(T, E), default: E) -> E
fn map_ok(result: Result(T, E), f: T -> U) -> Result(U, E)
fn map_error(result: Result(T, E), f: E -> F) -> Result(T, F)
fn and_then(result: Result(T, E), f: T -> Result(U, E)) -> Result(U, E)
fn or_else(result: Result(T, E), f: E -> Result(T, F)) -> Result(T, F)
```

### Option operations

Option is represented as `Some(value) -> {:some, value}` and
`None() -> {:none}`:

```cure
fn some(value: T) -> Option(T) = Some(value)
fn none() -> Option(T) = None()
fn is_some(opt: Option(T)) -> Bool
fn is_none(opt: Option(T)) -> Bool
fn unwrap(opt: Option(T), default: T) -> T
fn map_option(opt: Option(T), f: T -> U) -> Option(U)
fn flat_map_option(opt: Option(T), f: T -> Option(U)) -> Option(U)
fn option_or(opt: Option(T), default: T) -> T
```

### Usage example

```cure
mod Example
  use Std.Core

  fn main() -> Atom =
    let result = ok(42)
    let doubled = map_ok(result, fn(x) -> x * 2)
    let value = unwrap_ok(doubled, 0)
    Std.Io.print_int(value)    # prints 84
```

---

## Std.List

27 functions. Recursive list processing. `uncons/1` and `split_first/2`
were added in v0.18.0 to exercise the new cons-pattern compiler.

```cure
@extern(:erlang, :length, 1)
fn length(list: List(T)) -> Int

fn is_empty(list: List(T)) -> Bool
fn head(list: List(T), default: T) -> T
fn tail(list: List(T)) -> List(T)
fn last(list: List(T), default: T) -> T
fn nth(list: List(T), idx: Int, default: T) -> T
fn cons(elem: T, list: List(T)) -> List(T)
fn append(a: List(T), b: List(T)) -> List(T)
fn concat(lists: List(List(T))) -> List(T)
fn reverse(list: List(T)) -> List(T)
fn map(list: List(T), f: T -> U) -> List(U)
fn filter(list: List(T), pred: T -> Bool) -> List(T)
fn foldl(list: List(T), acc: U, f: T -> U -> U) -> U
fn foldr(list: List(T), acc: U, f: T -> U -> U) -> U
fn flat_map(list: List(T), f: T -> List(U)) -> List(U)
fn zip_with(a: List(T), b: List(U), f: T -> U -> V) -> List(V)
fn take(list: List(T), n: Int) -> List(T)
fn drop(list: List(T), n: Int) -> List(T)
fn contains(list: List(T), elem: T) -> Bool
fn find(list: List(T), pred: T -> Bool, default: T) -> T
fn any(list: List(T), pred: T -> Bool) -> Bool
fn all(list: List(T), pred: T -> Bool) -> Bool
fn sum(list: List(Int)) -> Int
fn product(list: List(Int)) -> Int
fn count(list: List(T), pred: T -> Bool) -> Int

# v0.18.0
fn uncons(list: List(T)) -> Tuple              # %[[h], t] or %[[], []]
fn split_first(list: List(T), default: T) -> Tuple
```

Note: `foldl` and `foldr` use curried callbacks: `fn(x) -> fn(acc) -> ...`.

### Usage example

```cure
mod ListExample
  use Std.List

  fn main() -> Atom =
    let nums = [1, 2, 3, 4, 5]
    let doubled = map(nums, fn(x) -> x * 2)
    let evens = filter(doubled, fn(x) -> x % 4 == 0)
    let total = sum(evens)
    Std.Io.print_int(total)   # 4 + 8 = 12
```

---

## Std.Math

18 functions. Arithmetic, trigonometric helpers, and safe division.

```cure
@extern(:erlang, :abs, 1)
fn abs(x: Int) -> Int

@extern(:math, :sqrt, 1)
fn sqrt(x: Float) -> Float

@extern(:math, :pow, 2)
fn pow(base: Float, exp: Float) -> Float

@extern(:math, :log, 1)
fn log(x: Float) -> Float

@extern(:math, :log2, 1)
fn log2(x: Float) -> Float

@extern(:math, :log10, 1)
fn log10(x: Float) -> Float

@extern(:math, :ceil, 1)
fn ceil(x: Float) -> Float

@extern(:math, :floor, 1)
fn floor(x: Float) -> Float

@extern(:erlang, :round, 1)
fn round(x: Float) -> Int

@extern(:math, :pi, 0)
fn pi() -> Float

fn max(a: Int, b: Int) -> Int
fn min(a: Int, b: Int) -> Int
fn clamp(value: Int, lo: Int, hi: Int) -> Int
fn sign(x: Int) -> Int
fn negate(x: Int) -> Int = 0 - x
fn is_even(x: Int) -> Bool = x % 2 == 0
fn is_odd(x: Int) -> Bool = x % 2 != 0
fn safe_div(a: Int, b: Int) -> Int = if b == 0 then 0 else a / b
```

### Usage example

```cure
mod MathExample
  use Std.Math

  fn hypotenuse(a: Float, b: Float) -> Float =
    sqrt(pow(a, 2.0) + pow(b, 2.0))

  fn main() -> Atom =
    let h = hypotenuse(3.0, 4.0)
    Std.Io.print_float(h)    # 5.0
```

---

## Std.String

17 functions. String manipulation via Erlang binary operations.

```cure
@extern(:erlang, :byte_size, 1)
fn length(s: String) -> Int

fn is_empty(s: String) -> Bool = s == ""
fn concat(a: String, b: String) -> String = a <> b

@extern(:string, :lowercase, 1)
fn downcase(s: String) -> String

@extern(:string, :uppercase, 1)
fn upcase(s: String) -> String

@extern(:string, :trim, 1)
fn trim(s: String) -> String

@extern(:string, :trim_leading, 1)
fn trim_leading(s: String) -> String

@extern(:string, :trim_trailing, 1)
fn trim_trailing(s: String) -> String

@extern(:erlang, :integer_to_binary, 1)
fn from_int(n: Int) -> String

@extern(:erlang, :float_to_binary, 1)
fn from_float(f: Float) -> String

@extern(:erlang, :atom_to_binary, 1)
fn from_atom(a: Atom) -> String

@extern(:erlang, :binary_to_integer, 1)
fn to_int(s: String) -> Int

@extern(:erlang, :binary_to_float, 1)
fn to_float(s: String) -> Float

@extern(:erlang, :binary_to_atom, 1)
fn to_atom(s: String) -> Atom

@extern(:binary, :split, 2)
fn split(s: String, sep: String) -> List(String)

@extern(:binary, :copy, 2)
fn repeat(s: String, n: Int) -> String

fn reverse(s: String) -> String
```

`reverse` works by converting to a charlist, reversing, and converting back.

---

## Std.Pair

9 functions. Tuple pair operations.

```cure
@extern(:erlang, :element, 2)
fn element(index: Int, tuple: Tuple) -> T

fn first(pair: Tuple) -> T = element(1, pair)
fn second(pair: Tuple) -> T = element(2, pair)
fn swap(pair: Tuple) -> Tuple = %[second(pair), first(pair)]
fn map_first(pair: Tuple, f: A -> C) -> Tuple
fn map_second(pair: Tuple, f: B -> C) -> Tuple
fn map_both(pair: Tuple, f: A -> C, g: B -> D) -> Tuple
fn to_list(pair: Tuple) -> List(T)
fn from_list(list: List(T)) -> Tuple
```

Tuples are constructed with `%[a, b]` syntax. `element` uses 1-based indexing
(Erlang convention).

---

## Std.Io

8 functions. Console output.

```cure
@extern(:io, :put_chars, 1)
fn put_chars(text: String) -> Atom

fn println(text: String) -> Atom = put_chars(text <> "\n")
fn print(text: String) -> Atom = put_chars(text)

@extern(:erlang, :integer_to_binary, 1)
fn int_to_string(n: Int) -> String

@extern(:erlang, :float_to_binary, 1)
fn float_to_string(f: Float) -> String

@extern(:erlang, :atom_to_binary, 1)
fn atom_to_string(a: Atom) -> String

fn print_int(n: Int) -> Atom = println(int_to_string(n))
fn print_float(f: Float) -> Atom = println(float_to_string(f))
```

---

## Std.Show

Protocol module. Defines `Show(T)` with `show(x: T) -> String`.

Implementations for Int, Float, String, Bool, Atom. Plus `show_line(x)` for
show-with-newline. See the [Protocols](/protocols) page for full details.

```cure
proto Show(T)
  fn show(x: T) -> String

fn show_line(x: T) -> String = show(x) <> "\n"
```

---

## Std.Eq

Protocol module. Defines `Eq(T)` with `eq(a: T, b: T) -> Bool`.

Implementations for Int, Float, String, Bool, Atom. Plus `ne/2`.

```cure
proto Eq(T)
  fn eq(a: T, b: T) -> Bool

fn ne(a: T, b: T) -> Bool = if eq(a, b) then false else true
```

---

## Std.Ord

Protocol module. Defines `Ord(T)` with `compare(a: T, b: T) -> Atom`.

Implementations for Int, Float, String, Atom. Returns `:lt`, `:eq`, or `:gt`.

```cure
proto Ord(T)
  fn compare(a: T, b: T) -> Atom

fn lt(a: T, b: T) -> Bool = compare(a, b) == :lt
fn le(a: T, b: T) -> Bool = compare(a, b) != :gt
fn gt(a: T, b: T) -> Bool = compare(a, b) == :gt
fn ge(a: T, b: T) -> Bool = compare(a, b) != :lt
```

---

## Std.Result

11 functions. Dedicated Result module (complements `Std.Core`'s result operations).

```cure
fn ok(value: T) -> Result(T, E)
fn error(reason: E) -> Result(T, E)
fn is_ok(result: Result(T, E)) -> Bool
fn is_error(result: Result(T, E)) -> Bool
fn unwrap(result: Result(T, E), default: T) -> T
fn unwrap_error(result: Result(T, E), default: E) -> E
fn map(result: Result(T, E), f: T -> U) -> Result(U, E)
fn map_error(result: Result(T, E), f: E -> F) -> Result(T, F)
fn and_then(result: Result(T, E), f: T -> Result(U, E)) -> Result(U, E)
fn or_else(result: Result(T, E), f: E -> Result(T, F)) -> Result(T, F)
fn flatten(result: Result(Result(T, E), E)) -> Result(T, E)
```

`flatten` unwraps a nested Result. `and_then` is monadic bind. `or_else`
handles the error path.

---

## Std.Option

10 functions. Optional values.

```cure
fn some(value: T) -> Option(T)
fn none() -> Option(T)
fn is_some(opt: Option(T)) -> Bool
fn is_none(opt: Option(T)) -> Bool
fn unwrap(opt: Option(T), default: T) -> T
fn map(opt: Option(T), f: T -> U) -> Option(U)
fn flat_map(opt: Option(T), f: T -> Option(U)) -> Option(U)
fn or_else(opt: Option(T), default: T) -> T
fn filter(opt: Option(T), pred: T -> Bool) -> Option(T)
fn zip(a: Option(T), b: Option(U)) -> Option(Tuple)
```

`zip` combines two Options into an Option of a pair. Both must be `Some`
for the result to be `Some`.

---

## Std.Map

14 functions. Backed by Erlang's `:maps` module.

```cure
fn new() -> Map
fn put(key: K, value: V, map: Map) -> Map
fn get(key: K, map: Map) -> V
fn get_or(key: K, map: Map, default: V) -> V
fn remove(key: K, map: Map) -> Map
fn has_key(key: K, map: Map) -> Bool
fn size(map: Map) -> Int
fn keys(map: Map) -> List(K)
fn values(map: Map) -> List(V)
fn to_list(map: Map) -> List(Tuple)
fn from_list(list: List(Tuple)) -> Map
fn merge(map1: Map, map2: Map) -> Map
fn is_empty(map: Map) -> Bool = size(map) == 0
fn count(map: Map) -> Int = size(map)
```

Note the argument order: `put(key, value, map)` follows Erlang's `:maps.put/3`
convention, not the `map |> put(key, value)` style.

---

## Std.Set

11 functions. Sets represented as maps with `:true` values.

```cure
fn new() -> Map = Std.Map.new()
fn add(elem: T, set: Map) -> Map
fn remove(elem: T, set: Map) -> Map
fn member(elem: T, set: Map) -> Bool
fn size(set: Map) -> Int
fn is_empty(set: Map) -> Bool
fn to_list(set: Map) -> List(T)
fn from_list(list: List(T)) -> Map
fn union(a: Map, b: Map) -> Map
fn intersection(a: Map, b: Map) -> Map
fn difference(a: Map, b: Map) -> Map
```

`intersection` and `difference` are implemented by folding over the first
set and checking membership in the second.

---

## Std.Functor

Protocol module. Defines `Functor(F)` with `fmap(container: F, f: A -> B) -> F`.

Currently implemented for `List` only.

```cure
proto Functor(F)
  fn fmap(container: F, f: A -> B) -> F
```

---

## Std.System

10 functions. System information and time.

```cure
@extern(:erlang, :system_time, 0)
fn monotonic_time() -> Int

@extern(:os, :system_time, 1)
fn system_time(unit: Atom) -> Int

fn timestamp_ms() -> Int = system_time(:millisecond)
fn timestamp_us() -> Int = system_time(:microsecond)

@extern(:erlang, :self, 0)
fn self() -> Pid

@extern(:erlang, :node, 0)
fn node() -> Atom

@extern(:erlang, :system_info, 1)
fn system_info(key: Atom) -> T

fn otp_version() -> T = system_info(:otp_release)
fn cpu_count() -> Int = system_info(:logical_processors)

@extern(:erlang, :halt, 1)
fn exit(code: Int) -> Atom
```

---

## Std.Fsm

12 functions. Runtime interface for spawning and interacting with compiled
FSM instances (gen_statem processes).

```cure
@extern(Elixir.Cure.FSM.Builtins, :fsm_spawn, 1)
fn spawn(fsm_module: Atom) -> Pid       # e.g. spawn(:"Cure.FSM.TrafficLight")

@extern(Elixir.Cure.FSM.Builtins, :fsm_spawn_named, 2)
fn spawn_named(fsm_module: Atom, name: String) -> Pid

fn stop(pid: Pid) -> Atom
fn send(pid: Pid, event: Atom) -> Atom
fn send_batch(pid: Pid, events: List(Atom)) -> Atom
fn get_state(pid: Pid) -> Tuple
fn state(pid: Pid) -> Atom
fn is_alive(pid: Pid) -> Bool
fn info(pid: Pid) -> Map
fn history(pid: Pid) -> List(Atom)
fn lookup(name: String) -> Pid
```

### Usage example

```cure
mod FsmExample
  use Std.Fsm

  fn main() -> Atom =
    let pid = spawn(:"Cure.FSM.TrafficLight")
    send(pid, :timer)
    let current = state(pid)
    Std.Io.println(Std.String.from_atom(current))
    stop(pid)
```

---

## Std.Vector

Length-indexed vectors with dependent types. Vectors are represented as
tagged tuples `{:vector, length, list}` where the length is tracked at
the type level.

```cure
fn empty() -> Tuple = %[:vector, 0, []]
fn singleton(x: T) -> Tuple = %[:vector, 1, [x]]
fn from_list(list: List(T)) -> Tuple
fn to_list(vec: Tuple) -> List(T)
fn length(vec: Tuple) -> Int
fn cons(x: T, vec: Tuple) -> Tuple        # length increments by 1
fn head(vec: Tuple) -> T                   # requires length > 0
fn tail(vec: Tuple) -> Tuple
fn append(a: Tuple, b: Tuple) -> Tuple     # length = len(a) + len(b)
fn map(vec: Tuple, f: T -> U) -> Tuple     # preserves length
fn is_empty(vec: Tuple) -> Bool
```

`cons` increments the tracked length. `append` sums the lengths of both
vectors. `head` on a zero-length vector returns the default value `0` --
a future version will enforce `n > 0` at the type level via dependent types.

---

## Std.Match

8 functions. Convenience helpers added in v0.18.0; every function is
implemented with nested destructuring as a smoke test for the new
pattern engine.

```cure
fn unpack_pair(t: Tuple) -> Tuple              # %[a, b]
fn fst(t: Tuple) -> T
fn snd(t: Tuple) -> T
fn head_tail(list: List(T), default: T) -> Tuple
fn uncons(list: List(T)) -> Tuple
fn first_two(list: List(T), default: T) -> Tuple
fn unwrap_ok(r: Result(T, E), default: T) -> T
fn unwrap_some(o: Option(T), default: T) -> T
```

Representative implementation:

```cure
fn first_two(list: List(T), default: T) -> Tuple =
  match list
    [h1 | t1] ->
      match t1
        [h2 | rest] -> %[h1, h2, rest]
        []          -> %[h1, default, []]
    []        -> %[default, default, []]
```

---

## Std.Test

5 functions. Basic assertion primitives for the `cure test` command.

```cure
fn assert(condition: Bool) -> Atom
fn assert_eq(a: T, b: T) -> Atom
fn assert_ne(a: T, b: T) -> Atom
fn assert_gt(a: T, b: T) -> Atom
fn assert_lt(a: T, b: T) -> Atom
```

All assertion functions return `:ok` on success or raise an error on failure.
Test files go in `test/` with function names starting with `test`:

```cure
mod MyTests
  use Std.Test

  fn test_addition() -> Atom =
    assert_eq(1 + 1, 2)

  fn test_list_length() -> Atom =
    assert_eq(Std.List.length([1, 2, 3]), 3)
```

Run with `cure test`.
