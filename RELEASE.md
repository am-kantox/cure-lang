# Cure v0.30.0 -- John
*A single panoramic diagnostic that gathers everything worth knowing
about Cure, the BEAM VM, the project, and the last few log entries,
exposed identically through a Mix task, an escript subcommand, and a
REPL meta-command. Named in tribute to John Carbajal.*

Cure is a dependently-typed programming language for the BEAM virtual
machine with first-class finite state machines and SMT-backed
verification.

v0.29.0 promoted the documentation surface to the same bar as the
language itself. With the docs caught up, v0.30.0 steps sideways and
gives the operator the one button that every dashboard has been quietly
missing: show me everything.

## Dedication

`john` is named for **John Carbajal**, a colleague who taught the
author that the most useful line in a fifty-page report is usually the
one nobody thought to print. This release is for him, and for the idea
that a diagnostic should first be overwhelming and only then selective.

## One feature, three surfaces, one implementation

Every call site produces the same report:

```bash
mix cure.john                                     # from a project checkout
cure john                                         # from the bundled escript
```

```text
cure(1)> :john                                    # from inside the REPL
```

Flags (`--width`, `--ansi` / `--no-ansi`, `--banner` / `--no-banner`,
`--root PATH`) are supported by both CLI surfaces; the REPL form
inherits the current session's theme and colour state.

## What is in the report

`Cure.John.collect/1` produces a plain Elixir map -- no PIDs,
references, or functions -- so the data can be serialised, piped into
a structured logger, or asserted against in tests:

- **Cure.** Version, escript entry, application loaded / started
  state, loaded-stdlib-module count, pipeline event-bus size,
  protocol registry size, UTC snapshot timestamp.
- **BEAM / OTP.** Elixir / OTP / ERTS versions, the full system
  banner, scheduler topology (online / total / dirty CPU / dirty I/O),
  logical-processor count, process / port / atom counts with their
  limits, ETS table count, memory breakdown (total / processes /
  binary / code / ETS / atom / system), reductions, runtime,
  wall-clock uptime, internal / external wordsize.
- **System.** OS family and version, architecture, hostname, user,
  home, cwd, and selected environment variables (`LANG`, `TERM`,
  `SHELL`, `PATH` entry count).
- **Tooling.** Resolved paths of `z3`, `git`, `make`, `cc`, plus
  loaded versions of every declared dependency.
- **Project.** When `Cure.toml` is present: name, version, root,
  source paths, lockfile presence, and the full dependency table with
  per-entry `version` / `path` / `git` markers. Absent
  `Cure.toml` is not an error -- the section just reads "(no
  `Cure.toml` found in the current directory)".
- **Runtime.** A condensed `Cure.Observe.Top` snapshot (supervisor /
  actor / FSM counts) plus the top five supervisors.
- **Doctor.** Severity counters from `Cure.Doctor.run/1` (info /
  warning / error) plus the overall `ok?` flag. The detail still
  lives behind `cure doctor`.
- **Recent logs.** Tails of up to five log files under
  `.cure/logs/*.log`, `_build/cure/logs/*`, or `erl_crash.dump`,
  sorted by mtime.

## Markdown rendering with a graceful fallback

`Cure.John.render/2` turns the map into CommonMark. `Cure.John.run/1`
prints it by routing through `Marcli.render/2` when the richer
renderer can load its MDEx NIF (plain Mix task, `iex -S mix`), and
falls back to the pure-Elixir `Cure.REPL.Markdown.render/2` when it
cannot. Inside the bundled `cure` escript the NIF path is not
loadable; the fallback keeps `cure john` looking identical to
`mix cure.john` across every environment.

## Public API

For programmatic consumers (tests, dashboards, structured loggers):

- `Cure.John.collect/1` -- gather the full snapshot as a plain map.
- `Cure.John.render/2` -- turn a snapshot into a Markdown string.
- `Cure.John.run/1` -- collect + render + write, returning the
  rendered string.

See [`docs/JOHN.md`](docs/JOHN.md) for the authoritative reference and
the full option list.

## Quiet elsewhere

Everything else in the release is housekeeping: `Cure.CLI` and the
REPL's `known_commands` lists now carry `john` / `:john` so typos get
a "Did you mean?" suggestion, `cure help` learnt the new subcommand,
and a handful of small bugfixes shipped in the process. The compiler
surface, the stdlib, the type checker, the FSM machinery, and the
package-registry story are unchanged from v0.29.

## Documentation

- `docs/JOHN.md` -- on-disk reference for the three surfaces plus the
  `Cure.John` API and the rendering-fallback behaviour. Added to the
  `mix.exs` docs extras list.
- `docs/REPL.md` -- `:john` added to the meta-command table.
- `site/priv/pages/tooling.md` -- new v0.30.0 section pointing at
  `cure john` and cross-linking to `docs/JOHN.md`.
- `site/priv/pages/repl.md` -- `:john` added to the meta-commands
  reference.
- `site/priv/pages/roadmap.md` -- new Implemented: v0.30.0 entry
  above v0.29.0.
- `site/priv/posts/2026/04-24-cure-v0.30.0.md` -- release blog post.

## Naming

"John" -- after John Carbajal, whose quiet talent for spotting the one
thing that actually mattered in a screen full of numbers made the
whole approach to this diagnostic obvious.

## What's next

The long-horizon items carry over unchanged:

- **Monomorphisation.** Specialise polymorphic functions whose call
  sites all use concrete types.
- **Profile-guided optimisation.** Feed `Cure.Profiler` data into the
  inliner and pattern-aware SMT encoder so hot paths get
  specialisation and cold paths stay small.
- **Time-travel for actors.** v0.28.0 added `@record` + `cure replay`
  for FSMs. The actor surface still needs journal hooks and a
  deterministic scheduler for reliable replay.
- **First-class Cure notebook format (`.cnb`).** Literate programming
  in Cure with type-checked code cells. The doc pipeline from
  v0.29.0 already covers most of the machinery.
- **WASM target.** Compile the Cure compiler via AtomVM so the
  Playground's type checker and sandbox can run entirely in the
  browser without a WebSocket round-trip.
