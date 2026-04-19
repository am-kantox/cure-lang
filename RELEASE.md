# Cure v0.23.0 -- Packaging, Proof, and Polish
*The long-awaited remote package registry, a property-based test
shrinker, two new stdlib modules, a health-check command, a
project-wide fixer, a telemetry bridge, coverage reporting, and the
cure_brainloop showcase example.*

Cure is a dependently-typed programming language for the BEAM virtual
machine with first-class finite state machines and SMT-backed
verification.

v0.22.0 closed out the language-surface backlog. v0.23.0 ships the
remote registry story that kept getting pushed -- with the rest of a
broad ergonomics upgrade so the day-to-day cycle catches up to the
language itself.

## Remote package registry

Six new modules under `Cure.Project.*`:

- `Cure.Project.Registry` -- read-only HTTP client over OTP's
  `:httpc`. Content-addressed, disk-cached, hash-verified responses.
- `Cure.Project.Lock` -- `Cure.lock` reader / writer with a
  `resolve_with_lock/2` entry point that short-circuits resolution
  when every constraint still accepts the locked version.
- `Cure.Project.Signing` -- Ed25519 keypair management and detached
  signatures over `name || NUL || version || NUL || sha256(tarball)`.
- `Cure.Project.Transparency` -- Rekor-style transparency-log
  verifier with Merkle-like chain checks.
- `Cure.Project.Publisher` -- assembles the tarball, signs it,
  uploads to the index.
- `Cure.Project.Json` -- minimal internal JSON codec so the compiler
  has no runtime JSON dependency.

Remote resolution is integrated into `Cure.Project.resolve_deps/1`:
any dependency without `path` or `git` is treated as a registry
dependency, fetched with hash check, signature-verified, unpacked
under `_build/deps/<name>-<version>/`.

## New CLI surface

- `cure publish` / `cure publish --dry-run` / `cure publish --hex`
- `cure search <query>` / `cure info <name>[:version]`
- `cure keys generate <handle>` / `cure keys list`
- `cure doctor` -- environment + project + source health report.
- `cure fix [--dry-run]` -- project-wide safe code rewrites.
- `cure test --cover` -- emits an HTML coverage report under
  `_build/cure/cover/`.

## Standard library (up to 27 modules)

- **`Std.Json`** -- encoder + decoder driven by a `Value` ADT
  (`Null | Bool | Num | Str | Arr | Obj`). Pairs with the v0.21.0
  `@derive(JSON)` extension.
- **`Std.Http`** -- thin wrapper over `:httpc`. `get`, `post`, `head`
  returning `Result(Response, HttpError)`. The Cure registry client
  dogfoods the same module.
- **`Std.Gen.shrink*`** and **`Std.Test.forall_shrunk`** -- shrinking
  primitives so property failures report minimised inputs instead of
  "it failed on a 47-element map".

## Infrastructure

- **`Cure.Telemetry`** -- optional `:telemetry` bridge that re-emits
  every `Cure.Pipeline.Events` event under
  `[:cure, :pipeline, <stage>, <event_type>]`. Production deployments
  can pipe compilation / Z3 latency into their existing observability
  stack without extra glue.
- **`Cure.Doctor`** -- structured diagnostic (Elixir / OTP / Z3 /
  registry URL / telemetry / project / source health).
- **`Cure.Fix`** -- five safe rewrites (line endings, trailing
  whitespace, tabs, blank-line runs, trailing newlines) across every
  `.cure` under `lib/` and `test/`.
- **`Cure.Cover`** -- `:cover` harness with HTML report generation.

## Showcase example

- `examples/cure_brainloop/` -- a toy expression-language
  interpreter with a REPL FSM. Exercises ADTs, records, refinement
  types, protocols, effects, FSM callback mode, OTP interop, FFI, and
  the new `Std.Json` module in one self-contained codebase. Ships
  with an ExUnit suite covering lexer, parser, evaluator, and
  environment semantics.

## Error catalog

Five new codes `E038`-`E042`:
- `E038 Registry Fetch Failed`
- `E039 Registry Hash Mismatch`
- `E040 Registry Package Not Found`
- `E041 Registry Signature Invalid`
- `E042 Transparency Log Unreachable`

## Documentation

- `docs/PACKAGE_REGISTRY.md` rewritten from a v0.17.0-era design
  document into the authoritative shipped contract.
- `docs/PUBLISHING.md` -- end-to-end walkthrough for generating keys,
  publishing a package, cross-publishing to Hex.pm, and enabling
  strict transparency-verification mode.

## Non-goals

- Private / enterprise registries.
- Binary artefacts other than `.beam` (no NIFs in the tarball).
- Automated yank UI (the API accepts yank metadata; no dedicated
  command).
- Pubgrub-based resolver (the v0.17.0 design doc's "fancy" variant;
  the deterministic backtracker stays).

## What's next

With the registry story closed, the v0.24.0 focus returns to the
language itself: monomorphisation, profile-guided optimisation, and
broader IDE integrations (Helix, Zed, upgraded VS Code extension).

## Naming

"Packaging, Proof, and Polish" -- three P's: the shipped package
registry, the proof-oriented shrinker, and the polish of
doctor / fix / coverage / telemetry.
