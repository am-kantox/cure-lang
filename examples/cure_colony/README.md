# cure_colony
A tiny typed supervision tree that exercises the three concurrency
primitives introduced in Cure 0.25.0:

* The Melquiades Operator `<-|` (unicode `✉`) for typed message sends.
* The `actor` container for writing typed worker processes.
* The `sup` container for declaring a supervisor tree.

## Sources
* `cure_src/colony.cure` --- declares two actor types (`Worker` and
  `Echo`) and a supervisor (`Colony`) that owns one instance of each.

## Compile and play
From the Cure repository root:
```
iex -S mix
```
Then, from the IEx shell:
```elixir
alias Cure.Compiler.Lexer
alias Cure.Compiler.Parser
alias Cure.Compiler.Codegen

{:ok, source} = File.read("examples/cure_colony/cure_src/colony.cure")
{:ok, tokens} = Lexer.tokenize(source, emit_events: false)
{:ok, asts}   = Parser.parse(tokens, emit_events: false)

# The parser returns a :block containing every container; compile them
# one by one so the supervisor's child specs can resolve the actor
# modules that were just loaded.
for ast <- elem(asts, 2) do
  {:ok, _} = Codegen.compile_module(ast, emit_events: false)
end

{:ok, root} = Cure.Sup.Runtime.start(:"Cure.Sup.Colony")
Cure.Sup.Runtime.which_children(:"Cure.Sup.Colony")

[{:worker_a, worker_pid, :worker, _} | _] =
  Cure.Sup.Runtime.which_children(:"Cure.Sup.Colony")

send(worker_pid, :inc)
send(worker_pid, :inc)
:"Cure.Actor.Worker".get_state(worker_pid)   # => 2

Cure.Sup.Runtime.stop(:"Cure.Sup.Colony")
```
From Cure source, the same dance reads:
```
mod Colony.Demo
  use Std.Supervisor
  use Std.Actor

  fn run() -> Int =
    let _  = Std.Supervisor.start(:"Cure.Sup.Colony")
    let kids = Std.Supervisor.which_children(:"Cure.Sup.Colony")
    let worker = first_worker(kids)
    worker <-| :inc
    worker <-| :inc
    Std.Actor.get_state(worker)
```
## What to read next
* `docs/SUPERVISION.md` --- full reference for actors, supervisors,
  and the Melquiades Operator.
* `lib/std/actor.cure`, `lib/std/supervisor.cure`, and
  `lib/std/process.cure` --- the Cure-facing stdlib modules.
* `lib/cure/actor/compiler.ex` and `lib/cure/sup/compiler.ex` ---
  the codegen that turns `actor` / `sup` into live BEAM modules.
