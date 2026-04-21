# Playground

The Cure Playground lives on `cure-lang.org/playground`. v0.27.0
ships the first half of the experience: a LiveView editor with
live syntax highlighting driven by `Makeup.Lexers.CureLexer`.

## What ships in v0.27.0

- Two-pane editor: plain-text source on the left, HTML-highlighted
  preview on the right.
- Debounced (150 ms) LiveView updates so the preview follows typing
  without saturating the socket.
- Tailwind-based layout that cooperates with the rest of the site.

## What lands in v0.28

- **In-browser type checker.** Extract the pure half of the Cure
  compiler -- lexer, parser, bidirectional checker, refinement
  translator (no Z3), formatter, printer -- into a standalone OTP
  application and load it from the site at runtime.
- **Sandboxed evaluator.** A server-side entry point that spawns an
  isolated BEAM process per request with `:erlang.spawn_opt/2`,
  hard memory + message queue limits, and a 2-second kill timer.
- **WASM target.** Compile the same pure compiler library to WASM
  via the AtomVM target so the docs pages can embed truly
  in-browser executable snippets.

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
- Route wired at `/playground` via `CureSiteWeb.Router`.
- HTML formatter: `Makeup.Formatters.HTML.HTMLFormatter`.
- Lexer: `Makeup.Lexers.CureLexer` (from the pre-existing
  `makeup_cure` Hex package).
