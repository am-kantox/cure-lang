# Cure REPL

Everything on this page landed in **v0.24.0**. Prior releases shipped an
`IO.gets`-backed line-mode loop; v0.24.0 replaces it wholesale with a
raw-mode line editor, live `Makeup`-powered syntax highlighting,
persistent history, incremental reverse search, Tab completion, a
minimal vi mode, and a `Marcli`-rendered `:help`. The architecture is
split across `Cure.REPL.{Terminal, LineEditor, History, Search,
Highlight, Theme, Completer, Render, Docs, Markdown}` so every piece
is individually testable.

The interactive REPL (`cure repl`) is a readline-grade environment for
evaluating Cure expressions, inspecting types and effects, and driving
ad-hoc experimentation with loaded modules.

Launch it with:

```sh
cure repl
```

The prompt reads `cure(N)>` where `N` is the expression counter. Every
submitted expression is wrapped into a synthetic `Repl.M<N>` module and
compiled + loaded on the fly; its `main/0` value is echoed back with an
ANSI-highlighted `=>` arrow.

## Key bindings (emacs mode)

### Cursor movement

- `Left` / `Right`               - move one grapheme
- `Ctrl+A` / `Home`              - beginning of line
- `Ctrl+E` / `End`               - end of line
- `Alt+B` / `Ctrl+Left`          - one word back
- `Alt+F` / `Ctrl+Right`         - one word forward

### Editing

- `Backspace` / `Ctrl+H`         - delete previous grapheme
- `Delete`                       - delete grapheme under cursor
- `Ctrl+D`                       - delete under cursor (or EOF on empty line)
- `Ctrl+K`                       - kill to end of line
- `Ctrl+U`                       - kill to start of line
- `Ctrl+W`                       - kill previous word
- `Alt+D`                        - kill next word
- `Ctrl+Y`                       - yank most-recent killed text
- `Alt+Y`                        - rotate the kill ring (after `Ctrl+Y`)
- `Ctrl+T`                       - transpose adjacent characters
- `Alt+T`                        - transpose adjacent words
- `Alt+U` / `Alt+L` / `Alt+C`    - upcase / downcase / capitalise word
- `Ctrl+_`                       - undo
- `Alt+_`                        - redo

### History

- `Up` / `Down`                  - step through history; drafts are preserved
- `Ctrl+R`                       - incremental reverse search
- `Ctrl+S`                       - forward search (while in search mode)
- `Ctrl+G` / `Esc`               - cancel search, restore original buffer

### Flow

- `Enter`                        - submit (auto-continues on unbalanced brackets)
- `;;` on its own line           - force-submit a multi-line buffer
- `Tab`                          - completion (meta-commands, paths, modules, keywords)
- `Ctrl+L`                       - clear screen
- `Ctrl+C`                       - abort current input; REPL stays running
- `Ctrl+D` on empty buffer       - exit

## Vi mode

`:mode vi` switches to a minimal modal editor; `Esc` enters normal
mode and `i` / `a` / `I` / `A` return to insert mode. Supported normal-mode
commands: `h`, `j`, `k`, `l`, `w`, `b`, `e`, `0`, `^`, `$`, `x`, `D`, `C`,
`u` (undo), `Ctrl+R` (redo). `:mode emacs` switches back.

You can also start directly in vi mode via `CURE_REPL_MODE=vi cure repl`.

## Meta-commands

### Types and effects

- `:t expr` (also `:type expr`)  - infer the type of `expr`
- `:effects expr`                - infer the effect set
- `:holes`                       - list holes from the last evaluation
- `:ast expr`                    - dump the parsed AST
- `:fmt expr`                    - pretty-print `expr`

### Modules and files

- `:load path`                   - compile and load a `.cure` file
- `:reload`                      - reload every previously loaded file
- `:use Mod`                     - bring `Mod`'s exports into scope
- `:env`                         - list all imports
- `:doc name`                    - show the docstring of `name`

### Session

- `:reset`                       - forget all bindings, fresh session
- `:save path`                   - write the session transcript to `path`
- `:edit`                        - open `$EDITOR` on the current buffer
- `:history [n]`                 - print the last `n` (default 20) entries
- `:search term`                 - non-interactive history grep
- `:clear`                       - clear screen

### Timing

- `:time expr`                   - evaluate and report elapsed wall time
- `:bench expr [n]`              - run `expr` `n` times, report min/avg/p95/max

### Appearance

- `:theme dark|light|mono`       - switch colour theme
- `:color on|off`                - toggle colour output
- `:mode emacs|vi`               - switch editing mode

### Quit

- `:help` / `:h`                 - show help
- `:quit` / `:q` / `:exit`       - leave the REPL

## Configuration

Programmatic options to `Cure.REPL.start/1`:

- `:history_path`  - override `~/.cure_history`
- `:raw`           - `true`, `false`, or `:auto` (default); forces the raw-mode editor
- `:theme`         - `:dark`, `:light`, `:mono`, or `:auto`
- `:mode`          - `:emacs` or `:vi`

Environment variables:

- `NO_COLOR`       - when set, forces the `:mono` theme
- `CURE_REPL_MODE` - `vi` to start in vi mode
- `VISUAL` / `EDITOR` - preferred external editor for `:edit`
- `TERM=dumb`      - disables colour and raw-mode editing

## History

Entries are persisted to `~/.cure_history` (atomic write-and-rename).
Consecutive duplicates are deduped and the file is capped at the most
recent 10,000 entries.

## Dependencies

The REPL builds on two companion libraries:

- [`makeup_cure`](https://hex.pm/packages/makeup_cure) -- Makeup lexer
  for the Cure language.
- [`marcli`](https://hex.pm/packages/marcli) -- Markdown-to-ANSI
  renderer and Makeup-token-to-ANSI formatter. `:help` and `:doc`
  output are pushed through `Marcli.render/2`.
