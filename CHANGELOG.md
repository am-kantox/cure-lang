# Changelog

All notable changes to Cure are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [0.24.0] -- The REPL You Deserve

v0.24.0 is the release where the interactive cycle catches up with
the rest of the language. The legacy `IO.gets`-backed REPL, present
since v0.15.0 and only lightly touched in v0.17.0, has been rewritten
whole-cloth on top of a raw-mode line editor with live syntax
highlighting, persistent history, incremental reverse search, Tab
completion, a minimal vi mode, and a Marcli-rendered `:help`. The
compiler itself is untouched; every change in this release is on the
read-eval-print side.

### Added -- REPL overhaul

The interactive REPL (`cure repl`) has been rewritten on top of a
raw-mode line editor with live syntax highlighting.

- `Cure.REPL.Terminal` puts stdin in cbreak/no-echo mode via `stty`,
  restores it on any exit path, and decodes raw byte streams into
  high-level key events (arrows, `Home`/`End`/`Delete`, `PgUp`/`PgDn`,
  `Ctrl+<letter>`, `Alt+<char>`, `Ctrl+Arrow`, F-keys, bracketed
  paste).
- `Cure.REPL.LineEditor` is a pure-function line buffer supporting
  cursor movement, word-wise movement, kill ring, yank, transpose,
  case changes, undo/redo and a minimal vi normal mode (`h/j/k/l`,
  `w/b/e`, `0`/`^`/`$`, `i/a/I/A`, `x`, `D`, `C`, `u`).
- `Cure.REPL.History` adds proper `Up`/`Down` navigation with draft
  preservation, consecutive-duplicate dedup, a 10,000 entry cap, and
  atomic write-and-rename persistence.
- `Cure.REPL.Search` implements `Ctrl+R` / `Ctrl+S` incremental
  reverse and forward search with an inverse-video status line and
  accept-and-edit semantics.
- `Cure.REPL.Completer` offers `Tab` completion for meta-commands,
  file paths (for `:load`/`:save`/`:edit`), loaded modules (for
  `:use`/`:doc`), theme / mode / colour argument literals, and Cure
  keywords.
- `Cure.REPL.Highlight` pipes input through `Makeup.Lexers.CureLexer`
  and `Marcli.Formatter` for live ANSI syntax highlighting, cached by
  buffer hash.
- `Cure.REPL.Theme` defines `:dark` (default), `:light`, and `:mono`
  presets; `NO_COLOR`, non-tty output, and `TERM=dumb` automatically
  drop to `:mono`.
- New meta-commands: `:history [n]`, `:search term`, `:clear`,
  `:save path`, `:edit`, `:time expr`, `:bench expr [n]`, `:ast expr`,
  `:theme dark|light|mono`, `:mode emacs|vi`, `:color on|off`. All
  existing meta-commands are preserved.
- `:help` output is rendered via `Marcli.render/2` so the key bindings
  table arrives as ANSI-styled Markdown.
- Non-tty stdin (CI, pipes) short-circuits to a legacy `IO.gets` loop
  so test automation continues to work.

### Added -- Dependencies

- `{:marcli, "~> 0.3"}` -- Markdown-to-ANSI renderer / Makeup ANSI
  formatter.
- `{:makeup, "~> 1.2"}` -- explicit dependency so `Makeup.Registry` is
  available at runtime.
- `{:makeup_cure, "~> 0.1"}` -- Cure language lexer for Makeup.

### Added -- Documentation

- `docs/REPL.md` -- full key-bindings table, meta-command reference,
  configuration, environment variables, vi-mode subset.
- `site/priv/pages/repl.md` -- user-facing REPL reference on
  [cure-lang.org](https://cure-lang.org) with the full key-bindings
  table and meta-command reference.

### Changed

- `mix.exs` version bumped to `0.24.0`. `Cure.CLI` banner and
  `cure version` output updated accordingly.
- `cure repl` defaults to raw-mode when stdin is a tty; the legacy
  line-mode loop is kept behind `Cure.REPL.start/1` `raw: false` and
  used automatically when the terminal cannot be put into cbreak mode.
- `Cure.Stdlib.Preload.preload/1` is invoked from `Cure.REPL.start/1`
  so expressions can reference `Std.List`, `Std.Math`, etc. without
  an explicit `:use`.

### Deferred to v0.25.0

- Monomorphisation of polymorphic functions whose call sites all use
  concrete types.
- Profile-guided optimisation wiring between `Cure.Profiler` and the
  inliner / pattern-aware SMT encoder.
- First-class Helix / Zed configurations and a VS Code extension
  upgrade to track the current LSP surface.
- REPL-level hot reload that recompiles-and-rebinds on every file
  save for long-running REPL sessions.

## [0.23.0] -- Packaging, Proof, and Polish

v0.23.0 ships the remote package-registry story that has been
rescheduled three releases in a row. It lands alongside a broad
ergonomics upgrade -- property-based shrinking, two new stdlib
modules, a doctor diagnostic, a project-wide fixer, a telemetry
bridge, coverage reporting -- and the `cure_brainloop` showcase
example that exercises every Cure feature in a single project.

### Added -- Remote package registry

- `Cure.Project.Registry` -- read-only HTTP client over OTP's
  `:httpc`. Implements the full endpoint set from
  `docs/PACKAGE_REGISTRY.md`: `GET /packages/:name`,
  `/packages/:name/:version`, `/packages/:name/:version/tarball`,
  `GET /packages?q=<query>`, `GET /log`, `POST /packages`. Content-
  addressed caching under `~/.cure/registry_cache/`. Emits `:registry`
  pipeline events for every network call (`:fetch_start`, `:fetch_ok`,
  `:fetch_failed`, `:cache_hit`, `:hash_mismatch`).
- `Cure.Project.Lock` -- `Cure.lock` reader and writer. Grows a
  `resolve_with_lock/2` entry point so `cure deps` can reuse the
  lockfile when every constraint is still satisfied.
- `Cure.Project.resolve_deps/1` extended: dependencies without `path`
  or `git` are treated as registry dependencies -- fetched, hash-
  checked, unpacked under `_build/deps/<name>-<version>/`, and added
  to the code path.
- `Cure.Project.Signing` -- Ed25519 key management on top of OTP
  `:crypto`. Keys under `~/.cure/keys/` with tight file perms. Signs
  `name || NUL || version || NUL || sha256(tarball)`. Verifies every
  install against the trusted-key list.
- `Cure.Project.Transparency` -- client-side verifier for the
  Rekor-style publish log. Canonicalises entries by key-sorted JSON,
  validates the Merkle-like hash chain, degrades gracefully to
  `{:ok, :unverified}` when `/log` is unreachable. Promotable to a
  hard failure with `config :cure, strict_transparency: true`.
- `Cure.Project.Publisher` -- assembles the package tarball, signs,
  and uploads. `build_hex_tarball/1` emits a Hex-compatible tarball
  (`VERSION` / `CHECKSUM` / `metadata.config` / `contents.tar.gz`)
  for cross-publishing via `mix hex.publish package --replace`.
- `Cure.Project.Json` -- minimal internal JSON codec used by every
  packaging module so the compiler has no runtime JSON dependency.

### Added -- CLI

- `cure publish`, `cure publish --dry-run`, `cure publish --hex`.
- `cure search <query>`, `cure info <name>[:version]`.
- `cure keys generate <handle>`, `cure keys list`.
- `cure doctor` -- environment / project / source health report,
  suitable as a CI gate.
- `cure fix [--dry-run]` -- project-wide safe rewrites
  (`normalize_line_endings`, `strip_trailing_whitespace`,
  `strip_mixed_tabs`, `collapse_blank_lines`,
  `ensure_trailing_newline`).
- `cure test --cover` -- runs the self-hosted test suite under
  `:cover`, emits an HTML index under `_build/cure/cover/`.
- New switches: `--dry-run`, `--hex`, `--handle`, `--token`,
  `--cover`, `--strict`, `--registry`.

### Added -- Standard library (brings total to 27)

- **`Std.Json`** (`lib/std/json.cure`) -- JSON encoder + decoder via
  the `Value = Null | Bool(Bool) | Num(Float) | Str(String) |
  Arr(List(Value)) | Obj(List((String, Value)))` ADT. Runtime is
  `:cure_std_json`. Companion to the v0.21.0 `@derive(JSON)` target.
- **`Std.Http`** (`lib/std/http.cure`) -- thin wrapper over `:httpc`.
  `get/1`, `get/2`, `post/3`, `head/1` returning `Result(Response,
  HttpError)`. Runtime is `:cure_std_http`.
- **`Std.Gen.shrink_int/1`**, **`shrink_list/1`**, **`shrink/1`** --
  shrinking primitives backing the property-based tests. Runtime is
  `:cure_std_gen`.
- **`Std.Test.forall_shrunk/3`** and
  **`Std.Test.forall_shrunk_default/2`** -- shrinking-aware property
  runner. Raises `{:property_failed_with_shrunk, value}` on the
  minimised counterexample. Runtime is `:cure_std_test`.

### Added -- Infrastructure

- `Cure.Telemetry` -- subscribes to every stage of
  `Cure.Pipeline.Events` and re-emits `[:cure, :pipeline, <stage>,
  <event_type>]` events through OTP's optional `:telemetry` library.
  Silent no-op when `:telemetry` is not on the load path.
- `Cure.Doctor` -- structured diagnostic (Elixir / OTP / Z3 /
  registry URL / telemetry / project / source health). Non-zero exit
  on any warning or error finding.
- `Cure.Fix` -- project-wide safe rewrites via `Cure.Fix.run/2`.
- `Cure.Cover` -- instrumentation harness around OTP's `:cover`;
  HTML report under `_build/cure/cover/`.

### Added -- Example project

- `examples/cure_brainloop/` -- the top-pick showcase from
  `stuff/ideas_for_cure_apps.md`. A toy expression-language
  interpreter with a REPL driven by a Cure FSM. Exercises ADTs,
  records, refinement types, protocols, effects, FSM callback mode,
  OTP interop, FFI, and the new `Std.Json` module in one coherent
  codebase. Ships with an ExUnit suite covering lexer, parser,
  evaluator, and environment semantics.

### Added -- Error catalog

Five new codes `E038` -- `E042`:
- `E038 Registry Fetch Failed`
- `E039 Registry Hash Mismatch`
- `E040 Registry Package Not Found`
- `E041 Registry Signature Invalid`
- `E042 Transparency Log Unreachable`

### Added -- Documentation

- `docs/PACKAGE_REGISTRY.md` rewritten from a v0.17.0-era design
  document into the authoritative shipped contract.
- `docs/PUBLISHING.md` -- end-to-end walkthrough for publishing a
  Cure package, including Hex cross-publishing and strict
  transparency-verification mode.

### Changed

- `mix.exs` version bumped to `0.23.0`. `:telemetry, "~> 1.3"`
  declared as an optional dependency. `:inets`, `:ssl`, `:crypto`,
  `:public_key` listed as `extra_applications` so the registry and
  signing code work out of the box.
- `Cure.toml` dependency parser recognises three forms:
  `name = { path = "..." }`, `name = { git = "...", tag = "..." }`,
  and the new bare `name = "<constraint>"` for registry deps.
- `cure deps` prefers the lockfile path when every constraint is
  still satisfied by the locked versions; otherwise falls back to
  fresh resolution and rewrites `Cure.lock`.

### Tests

- New test modules under `test/cure/project/`: `json_test.exs`,
  `lock_test.exs`, `signing_test.exs`, `transparency_test.exs`,
  `registry_test.exs`.
- New `test/cure/doctor_test.exs`, `test/cure/fix_test.exs`,
  `test/cure/telemetry_test.exs`.
- New `test/cure/stdlib/cure_std_json_test.exs`,
  `cure_std_gen_test.exs`, `cure_std_test_test.exs`.
- `examples/cure_brainloop/test/cure_brainloop_test.exs` covers the
  interpreter end-to-end.

## [0.22.0] -- Loose Ends

v0.22.0 closes three language-surface gaps that the v0.20.0 / v0.21.0
work scaffolded but deliberately left open, and elevates the v0.21.0
"Unreleased" first-class FSM overhaul into a shipped release. Lambdas
gain explicit multi-statement body shapes that work inside argument
lists, binary comprehension generators land (`for <<b <- buf>>`), and
trailing `rest::binary` segments now carry a `byte_size`-based
refinement so subsequent binary patterns type-check without having to
re-assert every invariant.

### Added -- Multi-statement lambda bodies

- `Cure.Compiler.Parser.parse_lambda_body/2` routes the body through
  a new `parse_lambda_block_body/2` dispatcher with four shapes:
  indented block (unchanged from v0.19.0), single expression
  (unchanged), brace-delimited `fn (x) -> { s1; s2; final }`, and
  `end`-terminated `fn (x) -> s1; s2; final; end`. The brace and end
  forms work inside argument positions where the lexer suppresses
  newlines and `:indent`/`:dedent` are never emitted.
- Both new forms compile to the same `{:block, meta, exprs}` AST
  node the indented form produces; `:block_shape` meta keys
  (`:brace` or `:end`) let the Printer and algebra formatter
  round-trip the author's chosen shape.
- `end` is now a reserved keyword (previously unused in `.cure`
  source). The lexer's `@keywords` list grows by one.
- `E035 Lambda Block Unterminated` error-catalog entry for an
  unclosed `{` or missing `end` inside a lambda body.

### Added -- Binary comprehension generators

- `Cure.Compiler.Parser.parse_generator_or_filter/1` dispatches on
  `:binary_open` and delegates to a new `parse_binary_generator/1`
  path. The resulting AST is `{:binary_generator, meta, [pattern,
  source]}` where `pattern` is the v0.21.0 `{:literal, [subtype:
  :bytes], segments}` shape and the segments are parsed at BP 42 so
  the trailing `<-` of the generator is not mis-tokenised as a
  less-than comparison inside `<<...>>`.
- `Cure.Compiler.Codegen.compile_comprehension/3` lowers
  `:binary_generator` qualifiers to Erlang's `b_generate` form
  inside the existing `:lc` comprehension so mixed qualifier lists
  still compile uniformly.
- `Cure.Types.Checker.do_infer/2` on `:comprehension` now binds
  every qualifier's pattern variables via `bind_pattern_vars/3` so
  the comprehension body type-checks with the generator variables
  in scope.
- `E036 Binary Comprehension Source Not Bitstring` error-catalog
  entry.

### Added -- `byte_size` arithmetic refinements

- `Cure.SMT.Translator` speaks `byte_size/1` as an uninterpreted
  `(Int) -> Int` function. Queries that reference `byte_size`
  prepend `(declare-fun byte_size (Int) Int)` and switch to the
  `QF_UFLIA` logic automatically.
- `Cure.Types.PatternRefinement.narrow/2` rewrites its binary-
  segment branch. Trailing `rest::binary` (`::bytes`, `::bitstring`,
  `::bits`) tails receive a refinement whose predicate captures
  `byte_size(__value__) == byte_size(__scrutinee__) - sum_of_preceding`,
  where the sum is the byte-aligned count of preceding segments. When
  any preceding segment's size cannot be linearised, the tail stays
  bound to plain `:bitstring` and the pipeline emits a
  `:refinement_ignored` event under code `E037`.
- `E037 Binary Segment Size Non-Linear` error-catalog entry.

### Added -- First-class FSM handling
- `Cure.FSM.State` -- the canonical runtime state record carried by
  every callback-mode FSM. A single struct with three fields:
  `:caller` (pid notified by lifecycle hooks), `:meta` (FSM-private
  bookkeeping), and `:payload` (user-visible domain value). Exposes
  `from_init/1`, `merge/2`, `notify/2`, `notify_self/1`, and the
  process-dictionary helpers `register_self/1` and `current/0`.
- Callback-mode FSMs generated by `Cure.FSM.Compiler` now store a
  `%Cure.FSM.State{}` as their primary state. The `start_link/1` entry
  point accepts three init shapes: a pre-built struct, a keyword list
  or map with `:caller`/`:meta`/`:payload` keys, or any bare value
  (treated as the initial `:payload` for backward compatibility).
- `on_transition` clauses now receive the struct as their 4th argument
  (`(current_state, event, event_payload, %FsmState{}) -> ...`) and
  may return either a full struct, a partial map containing
  `:payload` / `:meta` keys (merged into the current struct), or any
  bare value (interpreted as the new payload). The `:__same__` return
  path is unchanged.
- `on_enter`, `on_exit`, `on_failure`, `on_timer` receive the struct
  too.
- Two new lifecycle blocks: `on_start` (invoked inside `init/1`; may
  return `:ok`, `{:ok, full_or_partial_state}`) and `on_stop` (invoked
  from `terminate/2`).
- Three new `fsm` annotations:
  - `@initial :state_name` -- override the initial state.
  - `@notify_transitions` -- after every successful transition, send
    `{:cure_fsm, pid, {:transition, from, event, to, payload}}` to the
    caller.
  - `@auto_caller` -- when `:caller` is not explicitly provided, fall
    back to the spawning process registered via
    `:cure_fsm_spawner` in the FSM's process dictionary.
- Event payloads are a first-class concept: generated callback-mode
  FSMs expose `send_event/3` that wraps the event + payload into the
  `{:event, event, payload}` tuple already expected by `handle_cast`.
  `Cure.FSM.Runtime.send_event/3` and `Cure.FSM.Builtins.fsm_send_with/3`
  surface the same.
- `Std.Fsm` (`lib/std/fsm.cure`) grows `spawn_with_payload/2`,
  `spawn_with/2`, `send_with/3`, `full_state/1`, `notify/1`, and
  `caller/1` for full caller/meta/payload control from Cure.
- Inside any lifecycle hook body, a bare `notify(msg)` call reaches
  the FSM's `:caller` (implemented as a private helper in the
  generated module, resolving to `Cure.FSM.State.notify_self/1`).
- `Cure.FSM.Runtime.spawn_fsm/2` accepts `:caller`, `:meta`,
  `:payload`, `:init`, and the legacy `:data`. By default the
  spawning process is installed as the FSM's caller, so notifications
  reach the expected pid without ceremony.
- `Cure.FSM.Runtime.get_fsm_state/1` and the generated FSM module's
  `get_fsm_state/1` expose the full struct (not just the payload).
- `Cure.FSM.Runtime.send_event/2,3` routes through the target FSM
  module's own `send_event/2,3` when available, so simple-mode
  (`gen_statem`) FSMs continue to receive bare event atoms, while
  callback-mode FSMs receive the `{:event, event, payload}` tuple.

### Changed -- cure_turnstile example
- `examples/cure_turnstile/cure_src/turnstile.cure` now owns every bit
  of state (coin count in `:payload`, passage count in `:meta`) and
  opts into `@notify_transitions`. The Elixir wrapper
  (`lib/cure_turnstile.ex`) no longer wraps a host GenServer: it just
  calls `Runtime.spawn_fsm`, forwards events, and exposes a `stats/1`
  helper that reads the `%FsmState{}` struct.

### Added -- Tests
- `test/cure/fsm/fsm_first_class_test.exs` -- 21 tests covering the
  struct helpers, the three `start_link/1` init shapes, `send_event/3`
  with payload, `@notify_transitions`, `on_start`, and
  `Cure.FSM.Runtime.spawn_fsm` option mapping.
- Turnstile test suite updated for the struct-backed state and
  extended with a `@notify_transitions` receive assertion.

### Notes on backward compatibility
Legacy callback-mode FSMs that accessed the 4th argument as a bare
data term continue to compile -- the return-value contract still
accepts bare values, which are interpreted as the new payload with
`:caller` and `:meta` left untouched. However, any code that reached
into the handler's 4th argument directly (e.g. `data + 1`) must now
destructure the struct (`%{payload: n}` -- map pattern against the
struct works because structs are maps) to read the underlying payload.
Simple-mode (`gen_statem`) FSMs are entirely unchanged.

`end` is a new reserved keyword. No `.cure` file in the stdlib or
examples uses `end` as an identifier, but third-party code that
does will need to rename the binding.

### Numbers

- 1114 tests pass (up from 1078; 3 doctests + 1111 tests);
  `mix credo --strict`: 0 issues across 142 source files;
  `mix cure.check.stdlib`: 25/25; `mix cure.check.examples`:
  44/44 (up from 40/40 -- 4 new example files:
  `lambda_block.cure`, `binary_comprehension.cure`,
  `byte_size_refinement.cure`, and the first-class FSM example).

### Deferred to v0.23.0

- Remote package-registry index service, publication signing, and
  Hex.pm cross-publishing -- the `Cure.Project.Registry` HTTP
  client, Ed25519 archive signing, and `cure publish --hex`
  export path remain rescheduled for v0.23.0.

---
## [0.21.0] -- Through the Segments

v0.21.0 turns the v0.20.0 AST scaffolding into user-visible features
and clears three language gaps that surfaced during the v0.20.0
cycle. The headline is full Erlang-style destructuring of binaries
in `match`, multi-clause function heads, and `let` bindings, with a
dedicated exhaustiveness pass and the corresponding `E031`
diagnostic. ADT constructor payloads now accept function arrows,
`type` ADT declarations parse multi-line, `let` bindings admit deep
destructuring, the algebra pretty-printer is promoted to be the
default formatter, and three new `@derive` targets (Functor,
Monoid, JSON) land on top of the existing Show/Eq/Ord trio.

### Added -- Binary destructuring

- `Cure.Types.Checker.bind_pattern_vars/3` grows a `:bin_segment`
  clause. Every `<<...>>` pattern in `match` arms, multi-clause
  function heads, and `let` bindings now introduces its inner
  variables with the type implied by the segment specifier:
  `integer`/`size(n)` -> `Int`, `float` -> `Float`,
  `utf8`/`utf16`/`utf32` -> `Char`,
  `binary`/`bytes`/`bitstring`/`bits` -> `Bitstring`.
- `Cure.Types.PatternChecker.check_binary_exhaustiveness/2` --
  dedicated Maranget-lite coverage analysis over a sequence of
  binary-pattern arms. A top-level wildcard, or the combination of
  an empty-binary arm and an open-ended tail arm, covers the
  scrutinee; otherwise a concrete witness (`"<<>>"` or
  `"<<_, _rest::binary>>"`) is reported under code `E031`.
- `Cure.Types.PatternRefinement.narrow/2` grows a binary-literal
  branch that narrows the scrutinee type through the segments and
  returns the variable bindings separately.
- `E031` Binary Pattern Not Exhaustive error-catalog entry with
  example and fix guidance.

### Added -- Let destructuring

- `let` bindings reuse the v0.18.0 deep-destructuring engine.
  `let Ok(x) = expr`, `let %[a, b] = pair`, `let [h | t] = xs`,
  `let Point{x, y} = p`, and `let <<tag, _::binary>> = buf` all
  bind the right variables with the right narrowed types.
- Non-exhaustive `let` patterns emit code `E034` as a warning; the
  binding still compiles, and Erlang's `=` raises at runtime on a
  failed match. Setting `partial: true` on the assignment metadata
  suppresses the warning.
- `E034` Let Pattern Not Exhaustive error-catalog entry.

### Added -- Multi-line `type` ADT declarations

- `parse_type_def/1`, `parse_type_variant/1`, and
  `parse_more_variants/1` accept the canonical multi-line ADT
  layout with leading `|` on every continuation line, or with the
  first variant on the same line as `=` and subsequent variants
  marked with `|`. An optional wrapping `:indent`/`:dedent` pair
  emitted by the lexer is absorbed by the type-def recogniser.
- `E033` Multi-line Type Layout Invalid error-catalog entry.

### Added -- ADT function-type payloads

- Validated: constructor payloads accept arbitrary type
  expressions including function arrows
  (`type Callback = On(Int -> Int) | Off` and
  `type Transform = Morph((Int, Int) -> Int) | Id`). Function-typed
  payloads compile to first-class functions and are callable from
  inside match arms.
- `E032` Function Type Payload Invalid error-catalog entry reserved
  for the case where a variant payload is not a resolvable type
  expression.

### Added -- `@derive(Functor, Monoid, JSON)`

- `Cure.Types.Derive.derive/3` gains three new targets:
  - `:functor` emits `fmap(x, f)` that applies `f` to every field.
    Intended for single-parameter records; works on any record.
  - `:monoid` emits `combine(a, b)` that pairwise combines every
    field with the `<>` operator. Users supply `empty/0`
    separately; the derivation does not guess a neutral element.
  - `:json` emits `to_json(x)` that renders a record as a JSON
    object string with field names as JSON keys. `from_json/1`
    is reserved for a future release.
- `can_derive?/1` extended accordingly.

### Added -- Algebra formatter is the default

- `cure fmt` now runs the Wadler/`Inspect.Algebra`-style pretty
  printer from v0.20.0 by default. The legacy byte-level formatter
  remains available via `cure fmt --safe`. `cure fmt --algebra`
  stays as a synonym for the default. `cure fmt --check` routes
  through the same algebra formatter so CI agrees with interactive
  use.

### Added -- Multi-clause parameter destructuring

- `Cure.Types.Checker.check_multi_clause/7` routes every clause
  parameter through `bind_pattern_vars/3` instead of only binding
  bare variables. ADT constructors, tuples, cons patterns, record
  patterns, and binary patterns in function heads now introduce
  their inner variables for the clause body.

### Added -- Std.Access (carried from 0.20.x)

- New `Std.Access` stdlib module implementing an Elixir-style
  `Access` behaviour for Cure. Self-hosted under
  `lib/std/access.cure` and dispatched through the existing
  `proto`/`impl` machinery.
- Core protocol `proto Access(C)` with callbacks `fetch/2`,
  `get_and_update/3`, and `pop/2`. Implementations are provided for
  `Map` (which also covers records, since records compile to maps
  with a `__struct__` discriminator) and for `List` interpreted as
  a keyword-style list of `%[key, value]` pairs. Popping from a
  map that carries a `:__struct__` key raises
  `:struct_pop_not_allowed`, matching Elixir's struct semantics.
- Direct helpers: `fetch/2`, `fetch_bang/2` (raises `:key_error`),
  `get/3` (with default), `get_and_update/3`, `pop/2`.
- Composable lens ADT `Accessor` with factories `key/1`,
  `key_default/2`, `key_bang/1`, `elem_at/1`, `at/1`, `all/0`,
  `filter/1`.
- Nested traversal helpers: `fetch_in/2`, `get_in/2`, `put_in/3`,
  `update_in/3`, `get_and_update_in/3`, `pop_in/2`, accepting a
  `List(Accessor)` path.
- `Cure.Stdlib.Preload` updated to load `Cure.Std.Access` alongside
  the rest of the stdlib beams.

### Added -- Examples

- `examples/binary_destructuring.cure`, `examples/adt_fn_payload.cure`,
  `examples/multi_line_adt.cure`, `examples/let_destructuring.cure`,
  `examples/json_derive.cure`.

### Added -- Docs

- `docs/BINARIES.md` -- authoritative binary pattern reference.
- `docs/LANGUAGE_SPEC.md` updates: multi-line ADT layout, ADT
  function-type payloads, `let` destructuring, binary patterns.
- `docs/TUTORIAL.md` -- new Chapter 11 "Binary parsing"; FSMs
  renumbered to Chapter 12.

### Numbers

- 1078 tests pass (up from 1050); `mix credo --strict`: 0 issues
  across 137 source files; `mix cure.check.stdlib`: 25/25;
  `mix cure.check.examples`: 40/40.

### Deferred to v0.22.0

- Multi-statement lambda bodies -- brace-delimited
  (`fn (x) -> { stmt1; stmt2; final }`) and `end`-terminated block
  forms for anonymous functions embedded in argument lists where
  the existing indented-block form is not usable.
- Binary comprehension generators (`for <<b <- buf>>`) -- the
  parser currently mis-tokenises `<-` inside `<<...>>` as a
  less-than comparison; a dedicated binary-generator path in
  `parse_generator_or_filter/1` will unlock this shape.
- Full byte-size refinement propagation through `rest::binary`
  tail segments -- v0.21.0 binds `rest` to plain `Bitstring`;
  v0.22.0 will emit
  `byte_size(rest) == byte_size(scrutinee) - sum_of_preceding_sizes`
  once the SMT translator grows the arithmetic support.

### Deferred to v0.23.0

- Remote package-registry index service, publication signing, and
  Hex.pm cross-publishing -- the `Cure.Project.Registry` HTTP
  client, Ed25519 archive signing, and `cure publish --hex`
  export path are rescheduled to v0.23.0 so that v0.22.0 can
  focus on closing out the lambda / binary language-surface work.

---

## [0.20.0] -- The Shape of Things

v0.20.0 is the AST-polish release. Plain `#` comments are now
first-class nodes in the tree, binary literals and patterns gain the
full Elixir-style segment grammar (`<<x::utf8, rest::binary>>`), a
Wadler/Inspect.Algebra-style pretty-printer replaces the historical
byte-level formatter in `--algebra` mode, and pattern narrowing can
expose disjoint-tag and literal-equality witnesses through
`Cure.Types.PatternRefinement`.

### Added -- Plain comment nodes

- `Cure.Compiler.Lexer.tokenize/2` gains a `preserve_comments: true`
  option. When set, plain `#` comments emit `:line_comment` tokens
  instead of being discarded; doc comments (`##`, `###`) continue to
  be preserved regardless.
- `Cure.Compiler.Parser` threads `:line_comment` tokens into the AST
  as `{:comment, [line:, col:], text}` nodes in top-level programs,
  container bodies, and block bodies. Indented comment-only lines
  that precede a block's `:indent` token are rerouted inside the
  block body so they attach to the surrounding scope.
- `Cure.Compiler.Codegen` and `Cure.Types.Checker` silently skip
  comment nodes so preserving them has no effect on compilation or
  type checking.

### Added -- Full bitstring segments

- `:colon_colon` lexer token for `::`, distinct from `:colon` (type
  ascription) and `:atom` (symbol literals).
- `Cure.Compiler.Parser.parse_binary_literal/1` now wraps every
  element of `<<...>>` in a `{:bin_segment, meta, [value]}` node.
  The meta carries normalised specifier keys: `:type` (`:integer`,
  `:float`, `:bits`, `:bitstring`, `:bytes`, `:binary`, `:utf8`,
  `:utf16`, `:utf32`), `:signedness` (`:signed`/`:unsigned`),
  `:endianness` (`:big`/`:little`/`:native`), `:size` (an AST node),
  and `:unit` (integer). Specifiers chain with `-`
  (`::binary-size(n)`); bare integers are shorthand for `size(n)`.
- `Cure.Compiler.Codegen` and `Cure.Compiler.PatternCompiler` emit
  full Erlang `:bin_element` forms with the correct size/type/unit/
  sign/endian tuples from the segment AST.
- `Cure.Compiler.Printer` round-trips segment AST back into surface
  syntax.

### Added -- Algebra formatter

- `Cure.Compiler.Algebra` -- an `Inspect.Algebra`-style pretty-printing
  document module with `empty`, `concat`, `nest`, `break`, `line`,
  `group`, `string`, `space`, and a `format/2` best-fit layout.
- `Cure.Compiler.AlgebraFormatter` -- AST-to-document renderer that
  walks top-level programs, containers, and blocks, and delegates
  per-node rendering to `Cure.Compiler.Printer`. Standalone
  `{:comment, ...}` nodes round-trip as `# <text>` lines; sequences
  are separated by blank lines.
- `Cure.Compiler.Formatter.format_algebra/2` runs the algebra
  formatter with round-trip verification: the result must re-parse
  to an AST structurally equal to the input (modulo comment
  placement and position metadata); otherwise the original source is
  returned unchanged.
- `cure fmt --algebra` opt-in CLI flag. The existing byte-level safe
  formatter remains the default for v0.20.0 and will be promoted to
  `--algebra` as the default in v0.21.0.

### Added -- Structural refinement narrowing

- `Cure.Types.PatternRefinement` -- `narrow/2` returns
  `{bindings, narrowed_scrutinee}` for any pattern against any
  scrutinee type. Literal sub-patterns produce refinement types
  (`{x: Int | x == 0}` for `0`); constructor patterns (`Ok(v)`,
  `Error(e)`) and map patterns with `kind: :tag` narrow the
  scrutinee to `{:variant, tag, args}`. Integrates with the existing
  `Cure.Types.Refinement` SMT representation.

### Changed

- `Cure.Compiler.Formatter` ships `format_algebra/2` alongside the
  existing safe `format/2`; neither replaces the other in v0.20.0.
- `Cure.Compiler.Printer.bytes_to_string/2` handles both segment AST
  and legacy flat-list bytes representations.
- `Cure.Types.Checker.do_infer` skips `{:comment, ...}` nodes and
  reports `:unit` for them.

---

## [0.19.0] -- Bring the Furniture

The v0.18.0 release deliberately stayed laser-focused on deep
destructuring. v0.19.0 brings the previously-deferred "furniture"
home: proof containers, `assert_type`, record field defaults,
`@derive(Show, Eq, Ord)` wiring, property-based testing, a lazy
iterator protocol, the first half of the package registry, mutual
recursion totality, and multi-head cons patterns.

### Added -- Language
- `proof` containers (new keyword) -- `proof Name.Path` compiles to a
  regular BEAM module but the type checker requires every binding to
  return `Eq(T, a, b)` or a refinement witness. Error code `E026`.
- `assert_type expr : T` -- compile-time type assertion that vanishes
  at runtime; errors surface as `E027`.
- Record field defaults: `rec Person\n  name: String = ""\n  age: Int = 0`.
  Construction merges declared defaults with user-supplied fields.
  Default type mismatches emit `E028`.
- `@derive(Show, Eq, Ord)` on `rec` -- wires `Cure.Types.Derive` end
  to end; synthesised functions are plain exports usable from any
  caller.
- Multi-head cons patterns: `[a, b | rest]` and deeper now parse,
  desugaring to right-associated cons cells.

### Added -- Standard library
- **`Std.Proof`** -- reflexivity-based laws (`plus_zero`, `zero_plus`,
  `plus_comm`, `append_nil`, `map_id`).
- **`Std.Gen`** -- tiny stateless generator API (`int_in/2`, `bool/0`,
  `one_of/2`, `list_of_int/3`, `list_int/3`).
- **`Std.Iter`** -- lazy iterator protocol; constructors `empty/0`,
  `from_list/1`, `range/2`; consumers `fold/3`, `take/2`, `to_list/1`.
- **`Std.Test.forall/3`** and **`Std.Test.forall_default/2`** --
  property-based runner backed by `Std.Gen`.

### Added -- Totality
- `Cure.Types.Totality.check_mutual/1` -- Tarjan SCC over a module's
  call graph. Non-trivial cycles are reported as `:ok` (structural
  decrease proved) or `:suspect` (`E029` for `@total true` callers).

### Added -- Packaging
- `Cure.Project.Version` -- SemVer + constraint parser (`~>`, `>=`,
  `<=`, `<`, `>`, `==`), compound constraints joined by `and`.
  MAJOR.MINOR is accepted as shorthand for MAJOR.MINOR.0.
- `Cure.Project.Resolver` -- deterministic backtracking resolver over
  a local registry. Conflicts surface as `E030`.

### Added -- Error catalog
- `E026` Proof Shape Mismatch.
- `E027` `assert_type` Failed.
- `E028` Record Default Type Mismatch.
- `E029` Mutual Recursion Not Structural.
- `E030` Package Version Conflict.

### Added -- Examples and docs
- `examples/defaults.cure`, `examples/derived_show.cure`,
  `examples/proof_laws.cure`, `examples/lazy_iter.cure`.
- `docs/PROOFS.md` -- proof containers + `assert_type` reference.

### Changed
- `Cure.Types.Type.subtype?` accepts `:atom` as an inhabitant of any
  `Eq(...)` type (proof atoms are erased at runtime as `:cure_refl`).
- `Cure.Compiler.Codegen` gains a per-module `records` registry plus
  a `@derive` expansion pass that runs before signature collection.
- Parser: `proof` added to the keyword list; `@derive(...)` decorators
  now attach to record containers; multi-head cons desugars in
  `parse_list_or_comprehension/1`.
- `Cure.Stdlib.Preload` preloads `Std.Match`, `Std.Proof`, `Std.Gen`,
  `Std.Iter`.

---

## [0.18.0] -- Deep Destructuring

`match` and `let` grow up. Patterns can now destructure arbitrary
nesting across tuples, lists (cons and fixed), maps, records, and ADT
constructors -- any combination, any depth. Along the way the pattern
engine gained a pin operator (`^x`), repeated-variable equality
guards, record field-punning shorthand, and a nested-exhaustiveness
analyser.

### Added -- Pattern engine

- `Cure.Compiler.PatternCompiler` -- a dedicated pattern-to-Erlang
  translator extracted from the old in-place `compile_pattern` in
  `Cure.Compiler.Codegen`. Every pattern shape recurses through this
  module rather than bottoming out at expression codegen.
- Map patterns now use `map_field_exact` (`K := V`) instead of the
  (wrong) `map_field_assoc` (`K => V`); matching a map pattern now
  actually matches the subject instead of silently succeeding.
- Record patterns: `Point{x: a, y: b}` in pattern position compiles to
  a map pattern with an exact `__struct__ := :point` tag and per-field
  exact matches. Unmentioned fields are open-matched.
- Record field punning: `Point{x, y}` is shorthand for
  `Point{x: x, y: y}`, both in patterns and in constructions.
- ADT constructor patterns and cons patterns recurse correctly through
  the new engine; `[Ok(x) | rest]` now binds `x`.
- Pin operator `^x` in pattern position compares against a
  previously-bound value by emitting a synthetic equality guard.
- Repeated variable occurrences in the same pattern emit synthetic
  equality guards too (`%[x, x]` matches only when both slots agree).

### Added -- Type checker

- `Cure.Types.Checker.bind_pattern_vars/3` rewritten for deep
  recursion. Tuple patterns narrow element-by-element from the
  scrutinee tuple type; map patterns narrow via the record schema
  (when the scrutinee is a record) or the map value type; record
  patterns resolve per-field via `Cure.Types.Env.lookup_type/2`.
- Nested exhaustiveness pass in `Cure.Types.PatternChecker.check_nested/2`
  -- a Maranget-style column walker that emits concrete missing
  witnesses (`%[Error(_)]`, etc.) for tuple-of-ADT scrutinees. The
  old flat classifier remains as a fast-path.
- New error codes `E021` -- `E025`: unknown record field in pattern,
  record pattern field type mismatch, non-literal map pattern key,
  unbound pin variable, non-exhaustive nested match.

### Added -- Parser

- `^` lexed as `:caret` and parsed as the pin prefix operator,
  producing `{:pin, meta, [inner]}`.
- Field-punning in record patterns and map literals: a bare
  identifier at a key position followed by `,` or `}` now desugars
  to `name: name`.

### Added -- Standard library

- `Std.Match` -- new module with destructuring helpers
  (`unpack_pair/1`, `fst/1`, `snd/1`, `head_tail/2`, `uncons/1`,
  `first_two/2`, `unwrap_ok/2`, `unwrap_some/2`); every function
  exercises the new pattern engine.
- `Std.List.uncons/1` and `Std.List.split_first/2` added using cons
  destructuring.

### Added -- Examples

- `examples/destructuring.cure` -- end-to-end showcase of nested
  tuples, maps, records, cons, ADT constructors, and the pin operator.
- `examples/json_tree.cure` -- small JSON-like interpreter driven
  entirely by nested destructuring.
- `examples/pattern_guards.cure` extended with record patterns,
  field-punning, and nested ADT destructuring.

### Added -- Documentation

- `docs/PATTERNS.md` -- authoritative pattern matching reference with
  Cure surface syntax, Erlang abstract-form mapping, and binding
  semantics.
- `docs/LANGUAGE_SPEC.md` pattern-matching section rewritten from a
  12-line stub to a full reference.
- `docs/TUTORIAL.md` -- new Chapter 4 "Destructuring in `match`" and
  renumbering of later chapters.

### Changed

- `Cure.Compiler.Codegen` structure gains `:pattern_guards` and
  `:pattern_dup_counter` fields used by `PatternCompiler` to
  accumulate synthetic guards.
- `Cure.Compiler.Formatter` (v0.17.0) -- a source-preserving
  formatter that normalises line endings, strips trailing whitespace,
  expands leading tabs into two spaces, collapses runs of blank lines
  to a single blank line, and canonicalises operator spacing.
  Operates directly on the source buffer rather than re-printing from
  the AST, so plain `#` comments, string/regex/char literals, and doc
  comments are preserved byte-for-byte. Every rewrite is
  round-trip-validated against the original AST before being returned,
  and the formatter degrades to the unchanged buffer on any mismatch
  or on unparseable input.
- `cure fmt --check` -- exits non-zero if any file would be
  reformatted, suitable for CI.
- `cure fmt --aggressive` / `--ast` -- opt-in access to the
  destructive AST pretty printer.
- `Cure.LSP.Server` advertises `documentFormattingProvider: true`
  again; the handler delegates to `Cure.Compiler.Formatter`.

### Deferred to v0.19.0

The original v0.18.0 "Bring the Furniture" items (`proof` containers,
`assert_type`, record defaults, `@derive`, property-based testing,
`Std.Iter`, package registry first half, mutual-recursion totality)
are moved to v0.19.0. The pin operator remains gated behind
`--experimental-pin` in v0.18.0 and is promoted to default in v0.19.0
once real-world feedback is in.

---

## [0.17.0] -- Proofs & Polish: Toward Idris

The dependent-typing core grows up and the everyday UX catches up.
Three themes land together: dependent-type maturation, friction-free
UX, and ecosystem groundwork.

### Added -- Dependent-type maturation (Theme A)
- `Cure.Types.Sigma` -- dependent pairs; `Sigma(name: T1, T2)` surface
  syntax, subtyping rules, `Type.resolve/1` integration.
- `Cure.Types.Pi` -- dependent function types with `:explicit`,
  `:implicit`, `:erased` parameter modes and an AST-based return type.
- `Cure.Types.Reduce` -- terminating normaliser for type-level
  arithmetic, booleans, comparisons, and pair projection.
- `Cure.Types.Equality` -- propositional equality (`Eq(T, a, b)`),
  `refl` constructor, `rewrite` eliminator; runtime-erased via
  `:cure_refl`.
- `Cure.Types.Unify` -- first-order unification with occurs check for
  implicit-argument inference; `:unification_trace` pipeline event.
- `Cure.Types.Holes` -- `?name` and `??` placeholders with goal-type
  and local-context reporting via the `:hole_goal` event.
- `Cure.Types.Totality` -- coverage + structural-recursion analysis;
  `:total | :partial | :unknown` classification; `@total true` decorator.
- `Cure.Types.PathRefinement` -- path-sensitive refinement flow along
  `if`/`match` guards.
- `Std.Equal` -- equality combinators (`refl`, `sym`, `trans`, `cong`).
- `Std.Refine` -- `NonZero`, `Positive`, `Negative`, `NonNegative`,
  `Percentage`, `Probability`, and predicate helpers.

### Added -- Friction-free UX (Theme B)
- `Cure.REPL` -- multi-line input, `:t`, `:doc`, `:effects`, `:load`,
  `:reload`, `:use`, `:holes`, `:env`, `:reset`, `:fmt`, `:help`,
  `:quit`. History persisted to `~/.cure_history`.
- `Cure.Watch` -- `cure watch` recompiles, checks, or tests on every
  change with a 200 ms debounce.
- `Cure.LSP.Server` -- inlay hints, signature help, formatting,
  prepareRename / rename, code lenses, semantic tokens, workspace
  symbols.
- Error catalog codes `E011`-`E020` in `Cure.Compiler.Errors` covering
  implicit-argument failures, sigma destructuring, totality,
  unfilled holes, refinement counterexamples, dependent-type
  mismatches, equality proof mismatches, and doctests.
- `cure new <name> [--lib | --app | --fsm]` with three templates.
- `Cure.lock` lockfile; `cure deps update`, `cure deps tree`;
  git-based dependency resolution in `Cure.Project.resolve_git_dep/2`.
- `cure bench` -- benchmark runner for `bench/**/*.cure`.
- `cure test --filter PATTERN --doctests`.
- `Cure.Doc.Doctests` -- harvests `cure>` / `=>` doctests from `##`
  blocks and runs them.
- `docs/TUTORIAL.md` -- ten progressive chapters.
- `docs/DEPENDENT_TYPES.md` -- full guide for the new type-system
  features.

### Added -- Ecosystem groundwork (Theme C)
- MIT `LICENSE` file.
- Complete `mix.exs` `package` block for Hex publication, including
  docs extras.
- `vscode-cure/` -- TypeScript/LSP VS Code extension scaffold with
  TextMate grammar and language configuration.
- `docs/PACKAGE_REGISTRY.md` -- design document for the v0.18.0+
  package registry.

### Changed
- `Cure.CLI`: adds `watch`, `new`, `bench`, `deps update`, `deps tree`,
  `why`; extended OptionParser switches.
- `Cure.Project`: `scaffold/2` supersedes `init/1`; lockfile and
  git-dep support.
- `Cure.Types.Type`: recognises `Sigma`, `DPair`, `Eq`, `Pi` names in
  `resolve/1`; subtyping for sigma/eq/pi; `display/1` covers new
  shapes.

### Numbers
- ~9 new Elixir modules, ~9 new test files, ~150 new tests.
- 2 new `.cure` stdlib modules (total now 20).
- 6 new examples; 3 new docs.

---

## [0.16.0] -- Finitomata-Inspired FSM Rewrite

Complete rethinking of FSM handling. The FSM definition and transition logic
now coexist in the same `.cure` file via callback mode, inspired by
[Finitomata](https://hexdocs.pm/finitomata). Simple mode remains
backward-compatible.

### Added -- Dual-Mode FSM Compilation
- **Callback mode**: FSMs with an `on_transition` block compile to
  `GenServer`-based modules with embedded transition tables, user-defined
  `on_transition/4` dispatch, and lifecycle callbacks
- **Simple mode** (backward-compatible): `gen_statem` codegen now includes
  `transitions/0` and `allowed/2` introspection, hard event auto-fire via
  `next_event` actions, and soft event silent catch-all clauses
- `Cure.Compiler` pipeline handles both modes transparently

### Added -- Event Suffixes
- **Hard events** (`event!`): auto-fire when the FSM enters a state where
  the event is the sole outgoing transition. Compiler verifies this constraint.
- **Soft events** (`event?`): failed transitions are silently swallowed
  without logging or calling `on_failure`

### Added -- Lifecycle Callbacks
- `on_enter` -- called after entering a state
- `on_exit` -- called before leaving a state
- `on_failure` -- called when a normal (non-soft) transition fails
- `on_timer` -- called periodically when `@timer <ms>` is set

### Added -- FSM Callback Clause Syntax
- Parser: `(pat1, pat2, ...) -> body` clause syntax for FSM callbacks
- Lexer: `fsm_transition_depth` tracking for `!`/`?` identifier suffixes
- Parser: `@timer <ms>` annotation support
- Parser: `event_kind` classification (`:hard`, `:soft`, `:normal`)

### Added -- Verifier Enhancements
- Hard event validation: `!` events must be the sole outgoing event
- `on_transition` coverage warnings for ambiguous transitions
- Informational pipeline events for coverage analysis

### Added -- Introspection API
- `transitions/0` -- compiled transition table (both modes)
- `allowed/2` / `allowed?/2` -- check transition validity
- `responds?/2` -- check event availability from a state (callback mode)
- `Cure.FSM.Runtime.allowed?/3` and `responds?/3` delegation

### Changed -- LSP
- Symbols: FSM transitions as children with event suffix and kind labels;
  callback blocks and `@timer` as FSM children; detail shows compilation mode
- Hover: `on_transition` and lifecycle callbacks show signature documentation;
  hard/soft event patterns show explanatory hover text
- Completions: FSM callback names offered inside FSM blocks

### Changed -- MCP
- `analyze_fsm`: reports compilation mode, timer, event kinds with suffixes,
  and callback blocks with clause counts
- `syntax_help("fsm")`: documents both modes, event suffixes, lifecycle callbacks

### Changed -- Printer
- Event suffix output (`!`/`?`) in transition rendering
- Callback block rendering in FSM output
- `@timer` annotation rendering

### Changed -- Examples
- `cure_turnstile/` rewritten to use callback mode with `on_transition`

---

## [0.15.0] -- Developer Experience

Public API for parsing and printing Cure source, an effect system for tracking
side effects through the type system, HTML documentation generation, a code
formatter, and an interactive REPL.

### Added -- Public API
- `Cure.quote/2` -- parse Cure source into MetaAST 3-tuples
- `Cure.quoted_to_string/2` -- convert MetaAST back to Cure source (round-trip capable)
- Clean entry point for tooling, macros, and metaprogramming

### Added -- Effect System
- `Cure.Types.Effects` -- infer side effects from function bodies
- Effect kinds: `:io`, `:state`, `:exception`, `:spawn`, `:extern`
- Effect checking: declared effects validated against inferred effects
- `@extern` classification by target module (`:io` -> IO, `:ets` -> state, etc.)
- Pipeline event emission (`:effects_inferred`) for effect inference results
- Pure functions identified for aggressive optimization

### Added -- Source Printer
- `Cure.Compiler.Printer` -- full AST-to-source printer covering all Cure constructs
- Handles literals, operators, bindings, conditionals, pattern matching, collections,
  comprehensions, lambdas, function definitions, containers (mod/rec/enum/proto/impl/fsm),
  type annotations, decorators, imports, exception handling
- Round-trip verified: `quote -> print -> re-quote` produces equivalent AST

### Added -- Documentation Generator
- `Cure.Doc.Extractor` -- extract structured documentation from module ASTs
  (functions, protocols, types, effects, visibility, guards, clauses)
- `Cure.Doc.HTMLGenerator` -- static HTML docs with dark/light theme (system preference),
  per-module pages, function signature rendering, effect badges
- `cure doc [path|dir]` CLI command

### Added -- Code Formatter
- `cure fmt [path|dir]` -- format `.cure` source files via parse-then-print
- Consistent indentation and style across projects

### Added -- Interactive REPL
- `cure repl` -- evaluate Cure expressions interactively
- Wraps input in temporary modules, compiles and executes on the fly

### Added -- Compiler Refactoring
- `Cure.Compiler.Token` -- extracted Token struct with type, value, line, col
- `Cure.Compiler.Parser.Precedence` -- extracted Pratt parser binding power table
  with operator category and symbol lookup

### Added -- Stdlib
- `Std.Test` (5 fns) -- assert, assert_eq, assert_ne, assert_gt, assert_lt
- Total: 18 stdlib modules

### Added -- Examples
- `dependent_types.cure` -- refinement types and guarded functions (12 examples total)

---

## [0.14.0] -- Real-World Readiness

A language is real-world ready when programs can have dependencies, protocols
work across module boundaries, and tests can be written in the language itself.

### Added -- Package Management (Phase 1)
- `Cure.Project` -- Cure.toml project file parsing (minimal TOML subset)
- `Cure.Project.resolve_deps/1` -- compile path-based dependencies, add to code path
- `Cure.Project.init/1` -- scaffold new projects with Cure.toml, lib/, test/
- `Cure.Project.compiler_opts/1` -- read compiler options from project config
- `cure init <name>` CLI command
- `cure deps` CLI command

### Added -- Cross-Module Protocol Dispatch (Phase 5)
- `Cure.Types.ProtocolRegistry` -- ETS-backed global protocol implementation registry
- `register_impl/4`, `lookup_impl/3`, `has_impl?/2`, `list_impls/1` APIs
- `list_impls_by_method/1` -- cross-protocol method lookup
- Started automatically in `Cure.Application`
- Used by codegen for cross-module protocol dispatch

### Added -- Testing Infrastructure (Phase 6)
- `cure test` CLI command -- compile and run `.cure` test files from test/
- Discovers functions starting with `test`, reports pass/fail counts
- `Std.Test` stdlib module -- assert, assert_eq, assert_ne, assert_gt, assert_lt

---

## [0.13.0] -- Depth Over Breadth

Deepened every subsystem from "working foundation" to "production ready."
Closed remaining gaps with the legacy Erlang implementation (~17,000 lines
ported, primarily the type optimizer and 5 LSP modules).

### Added -- Dependent Type Verification (Phase 1)
- Constrained function signatures stored in type env
- Call-site verification via SMT (`Cure.SMT.Solver.prove_implication/4`)
- Counterexample extraction from Z3 models via `Cure.SMT.Parser.parse_model/1`
- Type-level arithmetic in return types (`Vector(T, m + n)`)
- Value parameter parsing: `fn f(v: Vector(T, n: Nat))`
- `Std.Vector` stdlib module -- length-indexed vectors using dependent types

### Added -- Cross-Module Protocol Registry (Phase 2)
- ETS-backed global protocol registry started in `Cure.Application`
- Implementations registered during codegen, discovered at compile time
- `has_impl?` / `lookup_impl` APIs for protocol resolution
- `where Show(T)` constraint validation at call sites
- Cross-module `@derive(Show)` wired into codegen pipeline

### Added -- LSP Production Features (Phase 3)
- `textDocument/definition` with source location tracking
- Type holes: `_` in type annotations inferred and reported as LSP hint diagnostics
- Code actions: add missing match arms, add missing imports, typo correction
- Incremental compilation: AST caching per document URI + version
- Debounced diagnostic publication
- SMT feedback: refinement type info on hover, inline counterexamples

### Added -- Advanced Optimizer (Phase 4)
- Function inlining (small pure functions, recursion-safe)
- Monomorphization at concrete call sites
- Guard simplification (algebraic rules, clause merging, redundancy elimination)
- Pattern-aware SMT encoding for precise exhaustiveness checking
- Deep pipe chain optimizer (Result propagation, Ok wrap/unwrap elimination)
- 5 optimizer passes: inline, constant_fold, dead_code, pipe_inline, guard_simplify

### Added -- FSM Actions & Monitoring (Phase 5)
- Transition actions: `Red --timer--> Green do count = count + 1`
- Guard codegen on transitions: `Red --timer when count > 0--> Green`
- Supervisor-compatible FSM processes with health check API
- Automatic restart tracking (last event time, transition count, error count)

### Added -- Error Reporting (Phase 6)
- CLI uses `format_with_source` for source-annotated errors with caret pointing
- Error catalog with codes E001-E005
- `cure explain E001` command with detailed explanations and examples
- "Did you mean?" suggestions wired into LSP code action quick fixes
- ANSI color output with TTY detection

### Added -- Stdlib Completion (Phase 7)
- `Std.Map` (14 fns) -- put, get, delete, merge, keys, values
- `Std.Set` (11 fns) -- add, remove, member, union, intersection
- `Std.Option` (10 fns) -- separate Option module from Std.Core
- `Std.Functor` (1 fn) -- functor protocol (map over any container)
- Total: 17 stdlib modules, ~200 functions

---

## [0.12.0] -- The Complete Rewrite

Completed the full rewrite from Erlang to Elixir, reimplementing all 12
phases of the original roadmap plus 8 additional phases of advanced features.

### Added -- Import Resolution (Phase A)
- `collect_imports/2` extracts module atoms from `use` declarations
- `resolve_import/3` checks imported modules for matching exports at compile time
- `collect_local_fn_names/1` ensures local functions take priority over imports
- Supports `use Std.List`, `use Std.{List, Core}`

### Added -- Dependent Types (Phase B)
- `Cure.Types.Dependent` -- dependent type representation with value parameters
- Type-level expression substitution
- Verification condition generation for SMT
- Compatibility checking

### Added -- Typeclass Derive (Phase C)
- `Cure.Types.Derive` -- auto-derive Show, Eq, Ord from type structure
- Generates protocol method AST from type name + field list

### Added -- LSP Enhancements (Phase D)
- `Cure.LSP.Symbols` -- symbol extraction from parsed AST
- Hierarchical DocumentSymbol format for `textDocument/documentSymbol`

### Added -- SMT Depth (Phase E)
- `Cure.SMT.Parser` -- Z3 S-expression output parser
- `parse_model/1` extracts variable -> value maps from `(get-model)` output
- General `parse_sexp/1` for nested S-expressions

### Added -- FSM Depth (Phase F)
- `Cure.FSM.TypeSafety` -- FSM transition consistency analysis
- Duplicate transition detection, wildcard shadow detection, self-loop detection

### Added -- Error Reporting Enhancements (Phase G)
- `Cure.Compiler.Errors.suggest/2` -- Levenshtein-based "did you mean?" suggestions
- `format_with_source/3` -- source-annotated errors with caret pointing

### Added -- Remaining Stdlib (Phase H)
- `Std.Eq` (2 fns) -- equality protocol with impls for all primitives
- `Std.Ord` (5 fns) -- ordering protocol with compare, lt, le, gt, ge
- `Std.Result` (11 fns) -- dedicated Result module with flatten

### Stats
- 569 tests, all passing
- 0 credo issues (strict mode)
- 0 compilation warnings
- 44 Elixir source files (~11,500 lines)
- 12 stdlib `.cure` modules (~160 functions)
- 10 example programs
- 4 documentation guides

---

## [0.11.0] -- First Roadmap Complete (Phases 1-12)

### Added -- Standard Library (Phase 1)
- 9 self-hosted stdlib modules (~140 functions) written in Cure itself
- `Std.Core` (36 fns) -- identity, compose, pipe, booleans, comparisons, Result, Option
- `Std.List` (25 fns) -- map, filter, foldl/foldr, flat_map, zip_with, take, drop
- `Std.Math` (18 fns) -- abs, sqrt, pow, log, ceil, floor, pi, max, min, clamp
- `Std.String` (17 fns) -- concat, split, trim, reverse, type conversions
- `Std.Pair` (9 fns) -- first, second, swap, map_first, map_second
- `Std.Io` (8 fns) -- println, print, type-to-string conversions
- `Std.System` (10 fns) -- timestamps, process info, system info
- `Std.Show` (protocol) -- Show with impls for Int, Float, String, Bool, Atom
- `Std.Fsm` (12 fns) -- spawn, send, state, history, lookup
- `mix cure.compile_stdlib` task

### Fixed -- Compiler Bugfixes (Phase 1)
- Lexer: blank/comment-only lines no longer break indentation
- Codegen: variable-as-function calls, lambda closure scoping, chained calls `f(x)(y)`
- Parser: qualified calls via dotted path reconstruction, guard binding power fix

### Added -- Protocol / Typeclass System (Phase 2)
- `Cure.Types.Protocol` -- protocol/impl tracking, type-to-guard mapping
- Codegen: 3-phase module body compilation (collect protos/impls, generate dispatch, compile)
- Type checker: protocol method signature registration, impl body validation
- Dispatch clause ordering by type specificity (Bool before Atom)

### Added -- SMT Solver + Refinement Types (Phase 3)
- `Cure.SMT.Process` -- Z3 GenServer via Erlang port, sentinel-based response parsing
- `Cure.SMT.Translator` -- MetaAST to SMT-LIB2, logic inference (QF_LIA/QF_LRA/QF_NIA)
- `Cure.SMT.Solver` -- check_sat, prove_implication, check_refinement_subtype
- `Cure.Types.Refinement` -- refinement type representation, SMT-backed subtype checking
- `Type.subtype?` extended for refinement-to-base and refinement-to-refinement

### Added -- Guard System Enhancements (Phase 4)
- `Cure.Types.GuardRefinement` -- guard constraint extraction, flow-sensitive refinement
- SMT-backed guard coverage analysis, unreachable clause detection
- Codegen fix: single-body functions with guards compile correctly
- Parser fix: guard expressions parse at BP 6 to stop before `=`

### Added -- Type-Directed Optimizations (Phase 5)
- `Cure.Optimizer` -- pass manager wired into compiler pipeline (`optimize: true`)
- `Cure.Optimizer.ConstantFold` -- arithmetic, boolean, comparison, string, unary folding
- `Cure.Optimizer.DeadCode` -- constant-condition branches, code after return/throw
- `Cure.Optimizer.PipeInline` -- identity elimination in pipe chains

### Added -- Pattern Exhaustiveness Checker (Phase 6)
- `Cure.Types.PatternChecker` -- classify patterns, compute coverage against scrutinee type
- Supports Bool, Result/Option ADTs, List, infinite types (require wildcard)
- Integrated into type checker as `:type_warning` pipeline events

### Added -- FSM Runtime (Phase 7)
- `Cure.FSM.Runtime` -- GenServer with ETS registry, event history, batch operations
- `Cure.FSM.Builtins` -- FFI bridge (fsm_spawn, fsm_send, fsm_state, etc.)
- Started automatically via Application supervisor

### Added -- Language Server Protocol (Phase 8)
- `Cure.LSP.Transport` -- Content-Length framing, JSON-RPC 2.0 over stdio
- `Cure.LSP.Server` -- initialize, textDocument lifecycle, diagnostics, hover, completions
- `cure-lsp` executable for editor integration
- `mix cure.lsp` task

### Added -- Standalone CLI (Phase 9)
- `Cure.CLI` -- escript entry point with 6 subcommands
- `cure compile|run|check|lsp|stdlib|version`
- Options: `--output-dir`, `--type-check`, `--optimize`, `--verbose`

### Added -- MCP Server (Phase 10)
- `Cure.MCP.Server` -- newline-delimited JSON-RPC with 7 tools
- Tools: compile_cure, parse_cure, type_check_cure, analyze_fsm, validate_syntax,
  get_syntax_help, get_stdlib_docs
- `mix cure.mcp` task

### Added -- Extended Examples & Documentation (Phase 11)
- 10 example programs: hello, math, traffic_light, list_basics, result_handling,
  pattern_guards, recursion, protocols, ffi, adt
- 4 doc guides: LANGUAGE_SPEC.md, TYPE_SYSTEM.md, FSM_GUIDE.md, STDLIB.md

### Added -- Profiler & Developer Tools (Phase 12)
- `Cure.Profiler` -- per-stage event counting, total time measurement
- `mix cure.profile` task

---

## [0.10.0] -- Project Bootstrap

Complete rewrite of Cure from Erlang to Elixir using Metastatic's MetaAST
format. Milestones 1-7 of the initial roadmap.

### Added -- Project Bootstrap & Lexer (Milestone 1)
- Elixir project with full tooling (credo, oeditus_credo, ex_doc, dialyxir, excoveralls)
- `Cure.Pipeline.Events` -- Registry-backed PubSub for pipeline stage events
- `Cure.Compiler.Lexer` -- tokenizes all Cure syntax keywords, operators, literals
- Indentation tracking (`:indent`, `:dedent`, `:newline` tokens)
- String interpolation tokenization
- Position tracking (line, column) on every token

### Added -- Parser: Expressions & Bindings (Milestone 2)
- Pratt (precedence-climbing) parser with indentation awareness
- All literal types, variables, binary/unary operators, function calls
- Let bindings, augmented assignment, conditionals, pattern matching
- Blocks, collections (list, tuple, map, range), pipe desugaring
- String interpolation, comprehensions, early return, throw, yield

### Added -- Parser: Definitions, Modules & FSMs (Milestone 3)
- Named function definitions (single-line, multi-line, multi-clause, guards, constraints)
- Modules, records, ADT/sum types, type aliases, refinement types
- Protocols, implementations, imports
- FSM definitions with transitions, wildcards, @terminal, @invariant, @verify
- Metastatic Cure adapter (ToMeta + FromMeta)

### Added -- BEAM Code Generation (Milestone 4)
- `Cure.Compiler.Codegen` -- MetaAST -> Erlang abstract forms
- Module assembly with exports, @extern wrappers, multi-clause functions
- ADT constructors as tagged tuples, records as maps
- `Cure.Compiler.BeamWriter` -- `:compile.forms/2` wrapper + `.beam` file writing
- `Cure.Compiler` -- orchestrator (lex -> parse -> codegen -> beam_write)
- `Mix.Tasks.Cure.Compile` -- `mix cure.compile` task

### Added -- Type System Foundation (Milestone 5)
- `Cure.Types.Type` -- canonical type representations, subtyping, join, AST resolution
- `Cure.Types.Env` -- scoped typing environment with builtins
- `Cure.Types.Checker` -- bidirectional type checker (infer + check modes)
- Two-pass module checking (signatures then bodies), @extern trusted

### Added -- FSM Compilation & Verification (Milestone 6)
- `Cure.FSM.Verifier` -- reachability (BFS), deadlock freedom, terminal state validation
- `Cure.FSM.Compiler` -- FSM MetaAST -> gen_statem Erlang abstract forms
- start_link, send_event, get_state, callback_mode, init, handle_event

### Added -- CLI, Error Reporting, CI, Examples (Milestone 7)
- `Cure.Compiler.Errors` -- structured error formatter for all pipeline stages
- GitHub Actions CI (`.github/workflows/ci.yml`)
- Example programs (hello.cure, math.cure, traffic_light.cure)
- Comprehensive README

### Stats
- 28 source files
- 290 tests, all passing
- 0 credo issues (strict mode)
- Clean dialyzer
