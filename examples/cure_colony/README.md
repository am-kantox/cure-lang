# cure_colony
A tiny typed supervision tree exercising the concurrency primitives
introduced in Cure 0.25.0:

* The Melquiades Operator `<-|` (unicode `✉`) for typed message sends.
* The `actor` container for writing typed worker processes.
* The `sup` container for declaring a supervisor tree.

The project is laid out as a standard Mix application: three `.cure`
files describe the processes, a `compile_cure` Mix task loads them into
the VM before Elixir compilation, and a thin `CureColony.Application`
starts the compiled supervisor as a child of a plain OTP supervisor.

## Layout
```
cure_src/
  worker.cure        # actor Worker  -> Cure.Actor.Worker
  echo.cure          # actor Echo    -> Cure.Actor.Echo
  colony.cure        # sup   Colony  -> Cure.Sup.Colony
lib/
  cure_colony.ex           # Elixir facade with helper functions
  cure_colony/
    application.ex         # OTP application that starts Cure.Sup.Colony
  mix/tasks/
    compile_cure.ex        # Mix.Tasks.CompileCure, invoked from mix.exs
test/
  cure_colony_test.exs
```

Each Cure file holds exactly one container. Every container type
(`mod`, `proof`, `fsm`, `actor`, `sup`) emits a `.beam` file to
`_build/cure/ebin/`; `actor` and `sup` modules are additionally loaded
into the VM eagerly during compilation so subsequent compilations in
the same pass can resolve the atoms immediately. That is why `mix.exs`
wires `compile_cure` into both the `compile` and `test` aliases -- it
rebuilds and reloads the three Cure modules in the current VM before
the Elixir code that depends on them runs.

## Build and test
```bash
cd examples/cure_colony
mix deps.get
mix test
```

The alias `test: ["compile_cure", "test"]` makes every `mix test`
first rebuild the three Cure modules in the current VM, then start the
application (which brings up `Cure.Sup.Colony` under
`CureColony.Supervisor`), then run the ExUnit suite.

## Interactive use
```bash
iex -S mix
```
The application has already started the colony:
```elixir
iex> Process.whereis(:"Cure.Sup.Colony")
#PID<0.123.0>

iex> Supervisor.which_children(:"Cure.Sup.Colony")
[
  {:echo,     #PID<0.126.0>, :worker, [:"Cure.Actor.Echo"]},
  {:worker_b, #PID<0.125.0>, :worker, [:"Cure.Actor.Worker"]},
  {:worker_a, #PID<0.124.0>, :worker, [:"Cure.Actor.Worker"]}
]

iex> worker = CureColony.worker_a()
iex> CureColony.inc(worker)
iex> CureColony.inc(worker)
iex> CureColony.worker_state(worker)
2

iex> CureColony.echo_message(:ping)
iex> CureColony.echo_state()
:ping
```

## Restart semantics
`Cure.Sup.Colony` uses a `:one_for_one` strategy with an intensity of
3 and a period of 5 seconds. Killing `worker_a` brings it back with a
fresh counter:
```elixir
iex> wa = CureColony.worker_a()
iex> CureColony.inc(wa)
iex> CureColony.worker_state(wa)
1

iex> Process.exit(wa, :kill)
iex> Process.sleep(20)
iex> wa2 = CureColony.worker_a()
iex> wa2 != wa
true
iex> CureColony.worker_state(wa2)
0
```

`worker_b` is configured `restart: :transient`, so a normal exit does
*not* spawn a replacement; `:echo` is `:permanent` with a 2 s
`shutdown` grace period, matching the declaration in `colony.cure`.

## What to read next
* [`docs/SUPERVISION.md`](../../docs/SUPERVISION.md) -- full reference for
  actors, supervisors, and the Melquiades Operator.
* [`lib/std/actor.cure`](../../lib/std/actor.cure),
  [`lib/std/supervisor.cure`](../../lib/std/supervisor.cure), and
  [`lib/std/process.cure`](../../lib/std/process.cure) -- the
  Cure-facing stdlib modules.
* [`lib/cure/actor/compiler.ex`](../../lib/cure/actor/compiler.ex) and
  [`lib/cure/sup/compiler.ex`](../../lib/cure/sup/compiler.ex) -- the
  codegen that turns `actor` / `sup` into live BEAM modules.
