# Cure v0.24.0 -- The REPL You Deserve
*A full rewrite of the interactive REPL: raw-mode line editor, live
syntax highlighting, persistent history, incremental reverse search,
Tab completion, minimal vi mode, and Marcli-rendered help.*

Cure is a dependently-typed programming language for the BEAM virtual
machine with first-class finite state machines and SMT-backed
verification.

v0.23.0 closed out the ecosystem backlog: remote package registry,
property-based shrinking, doctor / fix / telemetry / coverage. With
the language surface stable and the packaging story shipped, v0.24.0
steps back to the one piece of day-to-day UX that was still stuck in
2022: the interactive REPL. The read-eval-print loop has been
rewritten whole-cloth on top of a raw-mode terminal and a
pure-function line editor; the compiler itself is untouched.

## Raw-mode terminal

`Cure.REPL.Terminal` puts stdin into `cbreak`/no-echo mode via `stty`
and decodes raw byte streams into high-level key events. Supported
inputs:

- Arrow keys (`Left`, `Right`, `Up`, `Down`) plus word-wise
  `Ctrl+Left` / `Ctrl+Right`.
- `Home` / `End` / `Delete` / `PgUp` / `PgDn`.
- Every `Ctrl+<letter>` and `Alt+<char>` shortcut typical of a
  readline-grade editor.
- `F1` ... `F12` function keys.
- Bracketed paste (so multi-line pastes arrive as a single event).

The terminal is restored on every exit path: normal `:quit`, EOF on
an empty buffer, `Ctrl+C` on a non-empty buffer, uncaught exception,
SIGINT / SIGTERM. The raw-mode fallback on a non-tty stdin
(CI, pipes, `|` into `cure repl`) short-circuits to the legacy
`IO.gets` loop so test automation is unaffected.

## Pure-function line editor

`Cure.REPL.LineEditor` is a stateless buffer -- every key event
produces a new `%LineEditor{}` struct. That keeps the `raw_loop/2` a
straight recursive match on events, and makes the whole editor
trivially unit-testable.

Supported operations:

- Cursor movement: one grapheme, one word (`Alt+B` / `Alt+F` /
  `Ctrl+Left` / `Ctrl+Right`), start / end of line (`Ctrl+A` /
  `Ctrl+E` or `Home` / `End`).
- Editing: backspace / delete, kill to end (`Ctrl+K`), kill to start
  (`Ctrl+U`), kill previous word (`Ctrl+W`), kill next word
  (`Alt+D`), yank (`Ctrl+Y`), rotate yank (`Alt+Y`), transpose chars
  (`Ctrl+T`), transpose words (`Alt+T`), upcase / downcase /
  capitalise word (`Alt+U` / `Alt+L` / `Alt+C`).
- Undo / redo (`Ctrl+_` / `Alt+_`) backed by an append-only history
  of buffer snapshots.
- A minimal vi normal mode (`:mode vi`): `h` / `j` / `k` / `l`,
  `w` / `b` / `e`, `0` / `^` / `$`, `i` / `a` / `I` / `A`, `x`, `D`,
  `C`, `u`.

## Persistent history

`Cure.REPL.History` tracks every submitted expression in memory and
persists to `~/.cure_history` via atomic write-and-rename.

- Consecutive duplicates are deduplicated: `foo` followed by `foo`
  stores one entry.
- The file is capped at the most recent 10,000 entries.
- `Up` / `Down` step through history; the current draft is preserved,
  so scrolling up and back down returns to the exact buffer and
  cursor position you had.

## Incremental reverse search

`Ctrl+R` opens an inverse-video status line with the usual readline
semantics:

- Each new keystroke narrows the match; `Ctrl+R` again moves to the
  next older match; `Ctrl+S` flips direction to forward search.
- `Enter` accepts the match and submits it immediately;
  `Tab` / `ArrowLeft` / `ArrowRight` accept-and-edit it into the
  main buffer for further editing.
- `Ctrl+G` / `Esc` cancel and restore the original buffer.

## Live syntax highlighting

`Cure.REPL.Highlight` pipes every buffer state through
`Makeup.Lexers.CureLexer` and `Marcli.Formatter`, so expressions are
re-rendered as ANSI-coloured Cure source on every keystroke. The
highlighter caches by buffer hash so holding a key pressed doesn't
re-tokenise on every frame.

`Cure.REPL.Theme` ships three presets:

- `:dark` -- default; optimised for dark terminal backgrounds.
- `:light` -- inverted palette for light backgrounds.
- `:mono` -- no ANSI colour at all; forced automatically when
  `NO_COLOR` is set, when stdout is not a tty, or when `TERM=dumb`.

Toggle at runtime with `:theme dark|light|mono` or `:color on|off`.

## Tab completion

`Cure.REPL.Completer` handles four categories in one pass:

- Meta-commands: typing `:` and pressing `Tab` cycles through every
  registered command.
- File paths: inside `:load`, `:save`, `:edit`, completes against the
  filesystem.
- Loaded modules: inside `:use` and `:doc`, completes against
  currently-loaded Cure modules.
- Theme / mode / colour arguments, and Cure keywords in free form.

## Meta-commands

All existing meta-commands (`:t`, `:type`, `:effects`, `:load`,
`:reload`, `:use`, `:holes`, `:env`, `:reset`, `:fmt`, `:help`,
`:quit`) are preserved. v0.24.0 adds:

- `:history [n]` -- print the last `n` entries (default 20).
- `:search term` -- non-interactive history grep.
- `:clear` -- clear the screen.
- `:save path` -- write the session transcript to a file.
- `:edit` -- open `$EDITOR` (or `$VISUAL`) on the current buffer.
- `:time expr` -- evaluate and report elapsed wall time.
- `:bench expr [n]` -- run `expr` `n` times; report min/avg/p95/max.
- `:ast expr` -- dump the parsed AST.
- `:theme dark|light|mono`, `:mode emacs|vi`, `:color on|off`.

`:help` output is rendered through `Marcli.render/2`, so the
key-bindings table arrives as ANSI-styled Markdown with proper
boldface and alignment.

## New dependencies

Three small, focused libraries:

- `{:marcli, "~> 0.3"}` -- Markdown-to-ANSI renderer and Makeup
  token-to-ANSI formatter.
- `{:makeup, "~> 1.2"}` -- explicit so `Makeup.Registry` is available
  at runtime.
- `{:makeup_cure, "~> 0.1"}` -- Cure language lexer for Makeup,
  maintained alongside the compiler.

All three are Hex packages with narrow surface areas; none pull in
further transitive deps.

## Documentation

- `docs/REPL.md` -- authoritative key-bindings table, meta-command
  reference, configuration, environment variables, vi-mode subset.
- `site/priv/pages/repl.md` -- user-facing REPL reference on
  [cure-lang.org](https://cure-lang.org) rendered through the same
  markdown converter as the rest of the language guide.
- A dedicated blog post under `site/priv/posts/2026/` describes the
  motivation, the split-module architecture, and the design choices
  behind the rewrite.

## Non-goals

- No structural editing / paredit-style features. The editor operates
  on graphemes, not s-expressions.
- No remote / networked REPL. `cure repl` drives a local BEAM VM.
- No Windows console support. The raw-mode path relies on `stty` and
  ANSI escape codes; Windows users fall back to the legacy line-mode
  loop automatically.

## What's next (v0.25.0)

With the interactive cycle caught up, v0.25.0 returns to the type
pipeline:

- **Monomorphisation.** Specialise polymorphic functions whose call
  sites all use concrete types.
- **Profile-guided optimisation.** Feed profiler data into the
  inliner and pattern-aware SMT encoder.
- **IDE reach.** Ship first-class Helix and Zed configurations and
  upgrade the VS Code extension to track the current LSP surface.
- **REPL-level hot reload.** Recompile-and-rebind on every file save
  for long-running REPL sessions.

## Naming

"The REPL You Deserve" -- the interactive loop was the one piece of
UX that still felt 2022 after v0.23.0 shipped the registry story.
v0.24.0 puts it on par with the rest of the language.
