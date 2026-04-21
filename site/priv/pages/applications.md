%{
  title: "Applications",
  description: "First-class OTP applications and BEAM releases. The app container compiles a supervision tree into an Application callback module; cure release packages it as a bootable release.",
  order: 6
}
---
Cure 0.26.0 takes the supervision surface landed in v0.25.0 and wraps it in a full OTP application lifecycle. A project with a single `app` container compiles to three artefacts in one pass:

1. A loaded BEAM module `:"Cure.App.<Name>"` implementing the `:application` behaviour (`start/2`, `stop/1`, and, when applicable, `start_phase/3`).
2. An OTP `<name>.app` resource file written alongside every other Cure module under `_build/cure/ebin/`.
3. A bootable BEAM release under `_build/cure/rel/<name>/`, produced on demand by `cure release` (or `mix cure.release`).

The container slots in next to `actor` and `sup` from v0.25.0 and inherits their clause grammar (`on_start`, `on_stop`, and the new `on_phase :name` blocks).

## The `app` container

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
  on_phase :init
    (args, _kind, _start_args) -> init_phase(args)
  on_phase :warm_cache
    (_args, _kind, _start_args) -> Std.Cache.warm()
```

- `vsn`, `description`, `root`, `applications`, `included_applications`, `env`, and `registered` are top-level assignments inside the container body. Each one overrides the matching value in `[application]` (except `applications`, which is merged rather than replaced).
- `on_start` / `on_stop` reuse the FSM and actor callback-clause grammar (pattern tuple, optional `when` guard, body). Their bodies become the generated module's `start/2` and `stop/1` callbacks.
- Each `on_phase :name` block introduces a single three-argument clause `(phase_args, start_kind, start_args)` that feeds the generated `start_phase/3` callback.
- `root = ...` is optional. A phase-only application (say, a diagnostic that only runs its `on_phase :warm_cache` step and then stops) can omit it entirely; `start/2` then simply returns `{:ok, self()}`.

### Root supervisor resolution

`root = ...` accepts four forms, mirroring the `sup` child-spec conventions from [Actors](/actors):

- `root = sup Name` -> `:"Cure.Sup.Name"` (soft-keyword form; prefers the supervisor namespace).
- `root = Name` -> `:"Cure.Sup.Name"` (PascalCase identifier; same rule as a bare child entry in a `sup` tree).
- `root = App.Sub.Root` -> `:"App.Sub.Root"` (dotted path used verbatim, same as dotted child entries).
- `root = :my_app_sup` -> `:my_app_sup` (atom literal; escape hatch for arbitrary registered names).

### Single-`app` enforcement

`Cure.Project.compile_project/2` scans every `.cure` file under `lib/` and fails if more than one `app` container is declared:

```
error: duplicate application (E051)
 --> Cure.toml
  | more than one `app` container in the project:
  | lib/foo_app.cure -> app Foo
  | lib/bar_app.cure -> app Bar
```

The same diagnostic fires when the container's name does not match `[application].name` in `Cure.toml` (both names are normalised through `Macro.underscore/1`, so `app MyApp` matches `name = "my_app"`).

## `Cure.toml`: `[application]` and `[release]`

A project that ships an `app` container declares its application metadata next to the existing `[project]` / `[dependencies]` / `[compiler]` tables:

```toml
[project]
name          = "my_app"
version       = "0.1.0"
source_paths  = ["lib"]

[dependencies]

[compiler]
type_check = true
optimize   = true

[application]
name                  = "my_app"
vsn                   = "0.1.0"
description           = ""
applications          = ["logger", "crypto"]
included_applications = []
start_phases          = ["init", "warm_cache"]

[application.env]
port = 4000

[release]
name         = "my_app"
vsn          = "0.1.0"
include_erts = false
applications = ["logger"]
vm_args      = "rel/vm.args"
sys_config   = "rel/sys.config"
```

Notable rules:

- `[application].name` is the source of truth for the emitted `<name>.app` resource. The container's `app Name` just provides the BEAM module identity (`:"Cure.App.<Name>"`); the OTP application atom always comes from TOML.
- `[application].start_phases` is authoritative. Every entry must have a matching `on_phase :name` clause in the `app`, and every `on_phase` clause must appear in the list. Mismatches surface as `E053 Start Phase Mismatch`.
- `[application].applications` is merged with the container's own `applications = [...]` list, so the container can add dependencies (`:crypto`) without repeating what TOML already declares (`:logger`).
- `[release]` is only consulted by `cure release`. Omitting the whole table is fine; every field has a reasonable default derived from `[application]` and the running VM.
- The TOML parser accepts a minimal subset: scalar string / integer / bool / array-of-strings values, plus nested tables for `[application.env]`. Inline tables and mixed-type arrays are rejected.

## `cure release`

Once the project compiles cleanly, `cure release` (or `mix cure.release`) produces a self-contained BEAM release under `_build/cure/rel/<name>/`:

```
_build/cure/rel/my_app/
  lib/<app>-<vsn>/ebin/*.{beam,app}   # every included app
  releases/<vsn>/<name>.rel
  releases/<vsn>/start.boot
  releases/<vsn>/start.script
  releases/<vsn>/sys.config
  releases/<vsn>/vm.args
  bin/<name>                           # POSIX runner script
```

The runner script uses `${ERL:-erl}` so the release can be tested against any Erlang VM on `PATH`. Pass `--include-erts` (or set `[release].include_erts = true`) to bundle ERTS into the release directory itself -- the resulting tree is then fully self-contained.

### Application closure

The boot script needs a complete list of applications. `Cure.Release` seeds it with `:kernel`, `:stdlib`, `:compiler`, `:elixir`, the project's own application atom, and every entry in `[release].applications`. Out-of-tree dependencies must be loaded by the calling VM (typically by Mix when `cure release` runs through `mix cure.release`); the closure is read from the live code path.

### Runtime env access from Cure

Once the application is running, use `Std.App` to interact with it:

```cure
use Std.App

fn boot() -> Atom = Std.App.ensure_all_started(:my_app)
fn port() -> Int  = Std.App.get_env(:my_app, :port, 4000)
```

`Std.App` is a thin wrapper around `:application` that returns plain atoms and values rather than the OTP `{ok, _}` tuples. See [Stdlib](/standard-library) for the full nine-function surface.

## Error codes

The new codes are catalogued in `Cure.Compiler.Errors`. Run `cure explain <code>` for the full text:

- **E051 Duplicate Application** -- more than one `app` container in a project (or a name mismatch with `[application].name`).
- **E052 Missing Application** -- `cure release` invoked with no `app` declared.
- **E053 Start Phase Mismatch** -- TOML and container disagree on phase names.
- **E054 Unresolved Root Supervisor** -- `root = ...` does not resolve to a known module reference.
- **E055 Release Build Failed** -- wraps `:systools.make_script/2` or release-write I/O errors.

## Full example

[`examples/cure_forge/`](https://github.com/am-kantox/cure-lang/blob/main/examples/cure_forge) is the canonical end-to-end example. It ships as a small Mix project with three Cure source files wiring an application on top of four cooperating actors:

```cure
app CureForge
  vsn          = "0.1.0"
  description  = "Cure forge showcase: a typed OTP application"
  root         = sup Forge.Root
  applications = [:logger]
  env          = %{idle_timeout_ms: 5000, greeting: "forge ready"}
  on_start
    (_kind, _args) -> :ok
  on_stop
    (_state) -> :ok
  on_phase :warm_cache
    (_args, _kind, _start_args) -> :ok

sup Forge.Root
  strategy  = :one_for_one
  intensity = 5
  period    = 10
  children
    Metrics as metrics
    Logger  as logger  (restart: :permanent, shutdown: 2000)
    Queue   as queue   (restart: :transient)
    Pool    as pool    (restart: :permanent)
```

Each actor owns a narrow responsibility (counting events, buffering log lines, enqueuing work, or running a small worker pool) and exchanges messages with its peers through the Melquiades Operator `<-|`. The accompanying `CureForge` Elixir facade exposes the running tree to `iex -S mix` and to the ExUnit suite, so you can observe the application booting, exercise every actor, watch the supervisor restart a killed worker, and confirm that the `:warm_cache` start phase executed before the first request.

Read the project's [README](https://github.com/am-kantox/cure-lang/blob/main/examples/cure_forge/README.md) for the walk-through and [`docs/APP.md`](https://github.com/am-kantox/cure-lang/blob/main/docs/APP.md) for the on-disk reference that mirrors this page.
