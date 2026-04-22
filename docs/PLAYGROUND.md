# Playground

The Cure Playground lives on `cure-lang.org/playground`.

## v0.27.0 -- Syntax highlighting

- Two-pane editor: plain-text source on the left, Makeup-highlighted
  HTML preview on the right.
- Debounced (150 ms) LiveView updates so the preview follows typing
  without saturating the socket.
- Tailwind-based layout that cooperates with the rest of the site.

## v0.28.0 -- Live type checking + sandboxed evaluator

Both features from the v0.27.0 roadmap shipped in v0.28.0:

- **Live type-check panel.** Every debounced keystroke runs the full
  bidirectional checker (`Cure.Types.Checker`) on the source and
  renders the result below the highlighted preview. Green on success,
  red with formatted diagnostics on error.
- **Sandboxed evaluator.** `CureSiteWeb.Eval` spawns an isolated BEAM
  process via `:erlang.spawn_opt/2` with a 64 MB heap cap and a
  2-second kill timer. The child compiles the source, loads the
  module, calls `main/0`, and captures stdout. A "Run" button in the
  playground triggers it on demand.

## v0.29 -- WASM target

Compiling the pure compiler half (lexer, parser, bidirectional checker,
refinement translator without Z3, formatter, printer) to WASM via the
AtomVM target so docs pages can embed truly in-browser executable
snippets is deferred to v0.29.

## Running locally

The site lives under `site/` inside the repository. Boot it with:

```sh
cd site
mix setup            # first time
mix phx.server
```

Then open <http://localhost:4000/playground>.

## Architecture

- `CureSiteWeb.PlaygroundLive` in `site/lib/cure_site_web/live/`.
- `CureSiteWeb.Eval` in `site/lib/cure_site_web/eval.ex` -- sandboxed
  BEAM process with heap + time limits.
- Route wired at `/playground` via `CureSiteWeb.Router`.
- HTML formatter: `Makeup.Formatters.HTML.HTMLFormatter`.
- Lexer: `Makeup.Lexers.CureLexer` (from the `makeup_cure` Hex
  package).
- Type checker: `Cure.Types.Checker.check_module/2` called directly
  from the LiveView -- no extraction into a separate OTP app needed
  because `:cure` is already a path dependency of `cure_site`.
