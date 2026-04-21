# cure_forge

A fully-fledged OTP application exercising every primitive that Cure
0.26.0 ships:

- The **`app` container** (`forge_app.cure`), which compiles to
  `:"Cure.App.CureForge"` with `start/2`, `stop/1`, and `start_phase/3`
  callbacks plus an OTP `cure_forge.app` resource file.
- New **`[application]`** and **`[release]`** sections in
  `Cure.toml`, including a `start_phases = ["warm_cache"]` entry
  that matches the `on_phase :warm_cache` clause inside the container.
- The v0.25.0 **`sup` container** (`forge_root.cure`), which compiles
  to `:"Cure.Sup.Forge.Root"` and is wired as the application's
  `root`.
- Four **`actor` containers** (`metrics.cure`, `logger.cure`,
  `queue.cure`, `pool.cure`), each compiling to a loaded
  `GenServer` module named `:"Cure.Actor.<Name>"` and supervised
  under a `:one_for_one` strategy.
- **Message passing** between the actors and the Elixir facade --
  enqueue / dequeue through `Queue`, dispatch through `Pool`,
  accounting through `Metrics`. The facade uses the Elixir `send/2`
  primitive, which is exactly what the Melquiades Operator `<-|`
  lowers to in Cure source.
- The **`Std.App`** runtime surface (accessible through
  `Application.get_env/3` under plain Mix), so the application's env
  values round-trip end to end.

## Layout

```
Cure.toml                    # [project] + [dependencies] + [compiler]
                             # + [application] + [application.env] + [release]

cure_src/
  forge_app.cure             # app CureForge (root = sup Forge.Root)
  forge_root.cure            # sup Forge.Root (one_for_one over four actors)
  metrics.cure               # actor Metrics (request / error counters)
  logger.cure                # actor Logger  (bounded log buffer)
  queue.cure                 # actor Queue   (FIFO task queue)
  pool.cure                  # actor Pool    (single-threaded worker)

lib/
  cure_forge.ex              # Elixir facade wired to the running tree
  cure_forge/
    application.ex           # OTP Application callback (bridge for plain Mix)
  mix/
    tasks/
      compile_cure.ex        # Mix.Tasks.CompileCure, invoked by mix.exs

test/
  cure_forge_test.exs        # End-to-end ExUnit suite
  test_helper.exs
```

Every `.cure` file holds exactly one container. `actor`, `sup`, and
`app` modules are loaded into the VM eagerly during compilation, so
the `compile_cure` Mix task is wired into both the `compile` and
`test` aliases -- it rebuilds and reloads every Cure module in the
current VM before the Elixir code that depends on them runs.

## Build and test

```bash
cd examples/cure_forge
mix deps.get
mix test
```

The `test: ["compile_cure", "test"]` alias makes every `mix test`
first rebuild the six Cure modules in the current VM, then start the
application (which brings up `Cure.Sup.Forge.Root` under
`CureForge.Supervisor`), then run the ExUnit suite.

## Interactive use

```bash
iex -S mix
```

The application has already started the tree:

```elixir
iex> Process.whereis(:"Cure.Sup.Forge.Root")
#PID<0.123.0>

iex> Supervisor.which_children(:"Cure.Sup.Forge.Root")
[
  {:pool,    #PID<0.127.0>, :worker, [:"Cure.Actor.Pool"]},
  {:queue,   #PID<0.126.0>, :worker, [:"Cure.Actor.Queue"]},
  {:logger,  #PID<0.125.0>, :worker, [:"Cure.Actor.Logger"]},
  {:metrics, #PID<0.124.0>, :worker, [:"Cure.Actor.Metrics"]}
]

iex> CureForge.metrics()
%{requests: 0, errors: 0}

iex> CureForge.submit(:ok)
iex> CureForge.submit({:fail, :timeout})
iex> CureForge.submit(:ok)
iex> CureForge.drain_queue()
{:ok, 3}

iex> CureForge.pool_state()
%{done: 2, failed: 1}

iex> CureForge.metrics()
%{requests: 2, errors: 1}

iex> CureForge.log("booted")
iex> CureForge.log("first tick")
iex> CureForge.drain_log()
["booted", "first tick"]
# The logger buffers lines newest-first (cons prepend); the facade
# reverses on the way out so callers see insertion order.

iex> Application.get_env(:cure_forge, :greeting)
"forge ready"
```

## Data flow

```
submit/1 ---> Queue ---(dequeue)--> facade ---(Melquiades <-|)---> Pool
                                                                     |
                                                              (notify)|
                                                                     v
                                              facade ---(observe)--> Metrics
```

`drain_queue/0` is the Elixir counterpart of a Cure function that
would walk the queue, forward each `{:task, t}` to the pool with
`pool_pid <-| {:task, t}`, and, on each reply, observe the outcome
through `metrics_pid <-| {:observe, outcome}`. The facade uses plain
`send/2` (which is exactly what `<-|` compiles down to) so the
semantics are identical.

## Restart semantics

`Cure.Sup.Forge.Root` uses a `:one_for_one` strategy with an intensity
of 5 and a period of 10 seconds. Killing the pool brings it back with
fresh counters:

```elixir
iex> pool = CureForge.pool_pid()
iex> CureForge.submit(:ok)
iex> CureForge.drain_queue()
iex> CureForge.pool_state()
%{done: 1, failed: 0}

iex> Process.exit(pool, :kill)
iex> Process.sleep(20)
iex> pool2 = CureForge.pool_pid()
iex> pool2 != pool
true
iex> CureForge.pool_state()
%{done: 0, failed: 0}
```

`queue` is configured `restart: :transient`, so a normal shutdown
does *not* spawn a replacement; `pool`, `metrics`, and `logger` are
`:permanent`, with `logger` using a 2000 ms `shutdown` grace period
matching the declaration in `forge_root.cure`.

## Start phases

`[application].start_phases = ["warm_cache"]` in `Cure.toml` declares
one start phase, matched by the `on_phase :warm_cache` clause in
`forge_app.cure`. Mismatching names surface as `E053 Start Phase
Mismatch` at compile time.

Under `mix`, `CureForge.Application.start_phase/3` forwards the call
to the Cure-compiled `:"Cure.App.CureForge"`. Under `cure release`,
the OTP boot script calls the Cure-compiled module directly, without
any Elixir bridge in the way.

## Releases

```bash
cd examples/cure_forge
mix cure.release            # or: ./../../cure release
```

Produces a self-contained release under
`_build/cure/rel/cure_forge/`:

```
_build/cure/rel/cure_forge/
  lib/cure_forge-0.1.0/ebin/*.{beam,app}
  releases/0.1.0/cure_forge.rel
  releases/0.1.0/start.boot
  releases/0.1.0/start.script
  releases/0.1.0/sys.config
  releases/0.1.0/vm.args
  bin/cure_forge                            # POSIX runner
```

Pass `--include-erts` (or set `[release].include_erts = true`) to
bundle ERTS into the release directory.

## What to read next

- [`docs/APP.md`](../../docs/APP.md) -- full reference for the `app`
  container, `Cure.toml` sections, `cure release`, error codes.
- [`docs/SUPERVISION.md`](../../docs/SUPERVISION.md) -- the typed
  supervision surface (`actor`, `sup`, the Melquiades Operator).
- [`docs/STDLIB.md`](../../docs/STDLIB.md) -- the `Std.Actor`,
  `Std.Supervisor`, `Std.Process`, and `Std.App` runtime surfaces.
- [`site/priv/pages/applications.md`](../../site/priv/pages/applications.md)
  -- the user-facing reference mirrored on
  [cure-lang.org/applications](https://cure-lang.org/applications).
- [`lib/std/app.cure`](../../lib/std/app.cure),
  [`lib/std/actor.cure`](../../lib/std/actor.cure),
  [`lib/std/supervisor.cure`](../../lib/std/supervisor.cure),
  [`lib/std/process.cure`](../../lib/std/process.cure) -- the
  Cure-facing stdlib modules.
- [`lib/cure/app/compiler.ex`](../../lib/cure/app/compiler.ex),
  [`lib/cure/actor/compiler.ex`](../../lib/cure/actor/compiler.ex),
  [`lib/cure/sup/compiler.ex`](../../lib/cure/sup/compiler.ex) --
  the codegen that turns `app` / `actor` / `sup` into live BEAM
  modules.
