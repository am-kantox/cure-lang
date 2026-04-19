# Cure Tutorial
A guided tour of Cure for newcomers. Twelve short chapters take you
from an empty directory to a working project that uses dependent
types, deep destructuring, binary parsing, FSMs, the REPL, and the
type checker as a writing tool.
## 1. Hello, Cure
Install Cure (from the repo root):
```bash
mix deps.get
mix compile
mix escript.build
```
Now you have a `cure` binary in the project root. Add it to your PATH
and run:
```bash
cure version
```
Create a project:
```bash
cure new hello
cd hello
cure run lib/main.cure
```
You should see the project's hello message.
## 2. The compilation pipeline
Cure compiles `.cure` source through five stages: lex, parse, type
check, optimise, codegen. Every stage emits structured events you
can subscribe to from Elixir for tooling work.
Run `cure check lib/main.cure` to type-check without producing BEAM
output. Use it in your editor; you will see this command run on every
save once you turn on `cure watch lib/ --action check`.
## 3. Functions, records, ADTs
```cure
mod MyApp.Math
  type Sign = Positive | Negative | Zero

  fn classify(x: Int) -> Sign
    | x when x > 0 -> Positive
    | x when x < 0 -> Negative
    | _             -> Zero

  rec Point
    x: Int
    y: Int
```
- `fn` defines a function. Multiple clauses use `|`.
- `type` defines an ADT (sum type).
- `rec` defines a record (named product type).
## 4. Destructuring in `match`
Cure matches on structure, not just tags. Any combination of tuples,
lists, maps, records, and constructors can appear in a pattern and is
decomposed on the way in:
```cure
match value
  %[_, %{list: [head | tail]}, _] -> handle(head, tail)
  Person{name, address: Address{city}} -> greet(name, city)
  Ok(Some(v)) -> v
  _ -> default
```
Key shortcuts:
- `Point{x, y}` field punning -- equivalent to `Point{x: x, y: y}`.
- `^target` pin operator -- compare against a previously-bound value
  instead of binding fresh.
- Repeated variable names on the same pattern imply equality:
  `%[x, x]` matches only when both slots are equal.
Cons is single-head, so `[a, b | rest]` is not supported directly.
Use nested matches or `Std.Match.first_two/2`. See
`docs/PATTERNS.md` for the complete reference and
`examples/destructuring.cure` for a tour.
## 5. The REPL
```bash
cure repl
```
Try:
```
cure(1)> 1 + 1
=> 2
cure(2)> :t 42
42 : Int
cure(3)> :effects println("hi")
println("hi") :: ! Io
cure(4)> :load examples/recursion.cure
loaded examples/recursion.cure -> Cure.Recursion
```
Type `:help` for the full meta-command list. History is persisted to
`~/.cure_history`.
## 6. Refinement types
A refinement type constrains a base type with a logical predicate:
```cure
type NonZero = {x: Int | x != 0}

fn safe_div(a: Int, b: NonZero) -> Int = a / b
```
The compiler verifies the refinement at every call site using Z3.
Inside the function body, `b` has type `{x: Int | x != 0}`, so `a / b`
is safe.
The `Std.Refine` stdlib module collects useful aliases:
`Positive`, `Negative`, `Percentage`, `Probability`, ...
## 7. Path-sensitive refinement
When a variable appears in an `if` or `match` guard, its type is
*refined along the matching branch*:
```cure
fn safe_inv(x: Int) -> Int =
  if x != 0 then 1 / x else 0
```
Inside the `then` branch, the type checker knows `x : {x: Int | x != 0}`
and `1 / x` type-checks without an additional refinement annotation.
## 8. Sigma types
A Sigma type pairs a value with a type that may depend on it:
```cure
type Sized(T) = Sigma(n: Nat, Vector(T, n))
```
Use Sigma when a piece of data must carry the index it parametrises.
The type checker keeps `n` connected to the vector length through
the rest of the program.
## 9. Pi types and dependent return
```cure
fn append(xs: Vector(T, m), ys: Vector(T, n)) -> Vector(T, m + n)
```
The return type references the parameter names. At the call site, Cure
substitutes the actual values, normalises with `Cure.Types.Reduce`,
and compares the result. This means
`append(threeVec, threeVec)` is checked against `Vector(T, 6)`.
## 10. Holes and totality
While writing a function you don't yet know how to finish, leave a
hole:
```cure
fn safe_head(xs: List(T)) -> T = ?body
```
Compile, and Cure tells you the goal type and the local context.
Add `#[total]` above a function to require totality:
```cure
#[total]
fn factorial(n: Int) -> Int
  | 0 -> 1
  | n -> n * factorial(n - 1)
```
The totality checker classifies functions by coverage and structural
recursion. `factorial` is total because every recursive call shrinks
its structural argument (`n` -> `n - 1`).
## 11. Binary parsing
Cure supports full Erlang-style binary pattern matching in
`match` arms, multi-clause function heads, and `let` bindings.
Every segment is `value [:: specifier_chain]`; the specifier chain
is hyphen-joined and covers `integer`, `float`, `utf8`/`utf16`/`utf32`,
`binary`/`bytes`/`bitstring`/`bits`, signedness, endianness,
`size(expr)`, and `unit(n)`.
```cure
fn first_byte(buf: Bitstring) -> Int =
  match buf
    <<b, _rest::binary>> -> b
    <<>>                 -> 0
```
The type checker runs a dedicated exhaustiveness pass
(`Cure.Types.PatternChecker.check_binary_exhaustiveness/2`) that
reports `E031` when a set of arms does not cover every inhabitant
of the scrutinee. A match with at least one wildcard, or with both
an empty-binary arm (`<<>>`) and an open-ended tail arm
(`<<_, _rest::binary>>`), is exhaustive.
`let` bindings accept the same binary patterns:
```cure
fn parse_header(buf: Bitstring) -> Int =
  let <<tag, _rest::binary>> = buf
  tag
```
A non-exhaustive `let` emits `E034` as a warning; the binding still
compiles and Erlang's `=` raises at runtime on a failed match.
See `docs/BINARIES.md` for the authoritative reference and
`examples/binary_destructuring.cure` for an end-to-end walk-through.
## 12. FSMs
First-class finite state machines:
```cure
fsm Turnstile with Integer
  Locked   --coin-->  Unlocked
  Unlocked --push-->  Locked
  Unlocked --coin-->  Unlocked
  Locked   --push-->  Locked

  on_transition
    (:locked, :coin, _payload, data) -> %[:ok, :unlocked, data + 1]
    (:unlocked, :push, _payload, data) -> %[:ok, :locked, data]
    (_, _, _, data) -> %[:ok, :__same__, data]
```
The compiler verifies reachability and deadlock freedom and emits a
runnable `gen_statem` (or `GenServer` in callback mode) BEAM module.
## Where to next
- `docs/LANGUAGE_SPEC.md` -- syntax reference.
- `docs/TYPE_SYSTEM.md` -- type checker details.
- `docs/DEPENDENT_TYPES.md` -- the v0.17.0 dependent-typing layer.
- `docs/FSM_GUIDE.md` -- FSM mechanics in depth.
- `docs/STDLIB.md` -- standard library API.
- `docs/PACKAGE_REGISTRY.md` -- design notes for the eventual Cure registry.
