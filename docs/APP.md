# Applications and releases
Cure 0.26.0 introduces the `app` container, a first-class declaration
of an OTP application that lives next to the `actor` and `sup`
containers shipped in 0.25.0. A project that declares an `app`
gets, in addition to a runnable `Application` callback module, an
emitted `<name>.app` OTP resource file and a buildable BEAM release
via `cure release`.
The surface consists of three pieces:
1. The `app` container -- syntactic shape, lifecycle hooks, and
   start phases.
2. New `[application]` and `[release]` sections in `Cure.toml`.
3. The `cure release` subcommand (also available as
   `mix cure.release`).
## The `app` container
An `app` container declares the project's single OTP application:
```
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
* `vsn`, `description`, `root`, `applications`, `included_applications`,
  `env`, and `registered` are top-level assignments. They override the
  corresponding values in `[application]` (TOML wins on conflict for
  `applications`, which are merged).
* `on_start` and `on_stop` follow the same syntax as actor/FSM
  lifecycle hooks. Their bodies become the generated module's
  `start/2` and `stop/1` callbacks.
* `on_phase :name` introduces a single 3-argument clause
  `(phase_args, start_kind, start_args)` and feeds the generated
  `start_phase/3` callback.
The container compiles to a loaded BEAM module named
`:"Cure.App.<Name>"` that `use Application`. When `:output_dir` is
provided, the bytecode is also persisted alongside every other Cure
module. The module is never started automatically by the compiler;
it is started by the OTP boot script when the release boots, or
manually via `Std.App.ensure_all_started/1`.
### Root supervisor resolution
`root = ...` accepts four forms, mirroring the `sup` child-spec
conventions documented in `docs/SUPERVISION.md`:
* `root = sup Name`        -> `:"Cure.Sup.Name"` (the soft-keyword form).
* `root = Name`            -> `:"Cure.Sup.Name"` (PascalCase identifier).
* `root = App.Sub.Root`    -> `:"App.Sub.Root"` (dotted -- used verbatim).
* `root = :my_app_sup`     -> `:my_app_sup` (atom literal).
A phase-only application that does not need a root supervisor may
omit the `root` line entirely; `start/2` then returns `{:ok, self()}`
(matching what `:application` accepts).
### Single-`app` enforcement
Cure's project-wide compile driver
(`Cure.Project.compile_project/2`) scans every `.cure` file under
`lib/` and aborts when more than one `app` container is present:
```
error: duplicate application (E051)
 --> Cure.toml
  | more than one `app` container in the project:
  | lib/foo_app.cure -> app Foo
  | lib/bar_app.cure -> app Bar
```
The same code surfaces when the `app` container's name does not
match `[application].name` in `Cure.toml`. The match is performed
after both names have been normalised through `Macro.underscore/1`,
so `app MyApp` matches `name = "my_app"`.
## Cure.toml: `[application]` and `[release]`
A project that ships an `app` container declares its application
metadata under `[application]`, optionally complemented by a
`[release]` table:
```
[application]
name           = "my_app"
vsn            = "0.1.0"
description    = ""
applications   = ["logger", "crypto"]
included_applications = []
start_phases   = ["init", "warm_cache"]
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
* `start_phases` is authoritative. Every entry must have a matching
  `on_phase :name` clause in the `app`, and every `on_phase` clause
  must appear in the list. Mismatches surface as `E053 Start Phase
  Mismatch`.
* `applications` is merged with the container's own `applications =
  [...]` list; `[application].name` is the source of truth for the
  emitted `<name>.app` resource.
* The TOML parser accepts a minimal subset: scalar string / integer /
  bool / array-of-strings values, plus nested tables for
  `[application.env]`. More complex types (inline tables, mixed
  arrays) are not supported.
## `cure release`
Once the project compiles cleanly, `cure release` (or
`mix cure.release`) produces a self-contained BEAM release under
`_build/cure/rel/<name>/`:
```
_build/cure/rel/my_app/
  lib/<app>-<vsn>/ebin/*.{beam,app}    # for every included app
  releases/<vsn>/<name>.rel
  releases/<vsn>/start.boot
  releases/<vsn>/start.script
  releases/<vsn>/sys.config
  releases/<vsn>/vm.args
  bin/<name>                            # POSIX runner script
```
The runner script uses `${ERL:-erl}` so the release can be tested
against any Erlang VM on `PATH`. Pass `--include-erts` (or set
`[release].include_erts = true`) to bundle ERTS into the release
directory itself, which makes the resulting tree fully
self-contained.
### Application closure
The release boot script needs a complete list of applications.
`Cure.Release` seeds it with `:kernel`, `:stdlib`, `:compiler`,
`:elixir`, the project's own application atom, and every entry in
`[release].applications`. Out-of-tree dependencies must be loaded by
the calling VM (typically by Mix when `cure release` runs through
`mix cure.release`); the closure is read from the live code path.
### Stop / start phases / env at runtime
From a Cure module, use `Std.App` to interact with the running
application:
```
use Std.App
fn boot() -> Atom = Std.App.ensure_all_started(:my_app)
fn port() -> Int  = Std.App.get_env(:my_app, :port, 4000)
```
`Std.App` is a thin wrapper around `:application` that returns plain
atoms / values rather than the OTP `{ok, _}` tuples.
## Error codes
The new codes are catalogued in `Cure.Compiler.Errors`:
* **E051 Duplicate Application** -- more than one `app` container
  in a project (or a name mismatch with `[application].name`).
* **E052 Missing Application** -- `cure release` invoked with no
  `app` declared.
* **E053 Start Phase Mismatch** -- TOML and container disagree on
  phase names.
* **E054 Unresolved Root Supervisor** -- `root = ...` does not
  resolve to a known module reference.
* **E055 Release Build Failed** -- wraps `:systools.make_script/2`
  or release-write I/O errors.
Run `cure explain E054` (or any code) for the full catalog text.
## Example
The `examples/cure_colony/` project is the canonical end-to-end
example. After `mix cure.compile examples/cure_colony/cure_src` the
emitted `_build/cure/ebin/cure_colony.app` file is loadable with
`:application.load/1` and the release is buildable with
`mix cure.release`.
