%{
  title: "Playground",
  description: "The Cure Playground: a LiveView-based editor with live syntax highlighting. Type-checking and in-browser evaluation are on the roadmap for v0.28.",
  order: 13
}
---
The Cure Playground is an in-browser editor for exploring the Cure
syntax without installing anything locally. It is served from
[`/playground`](/playground); the LiveView re-highlights the source
on every keystroke using the same `Makeup.Lexers.CureLexer` that
drives the REPL.

## What ships in v0.27.0

The v0.27.0 Playground covers the first half of the planned
experience:

- A two-pane editor: the left pane is a plain-text textarea for
  source input, the right pane renders the Makeup-highlighted HTML
  output.
- Debounced LiveView updates (150 ms) so the preview follows typing
  without saturating the socket.
- Tailwind-based layout that adapts cleanly to dark and light
  system themes.

## What lands in v0.28

The in-browser type checker and bytecode evaluator are on track for
v0.28.0. The plan is to extract the pure half of the compiler --
lexer, parser, bidirectional type checker, refinement translator
without Z3, formatter, and printer -- into a standalone OTP
application. The site then loads that library at runtime and wires
the LiveView to call it; a sandboxed evaluator spawns an isolated
BEAM process per request with `:erlang.spawn_opt/2` and a 2-second
kill timer so user code cannot affect the server.

Parallel to the server-side path, the WASM path compiles the same
library via the AtomVM target so the Playground can run entirely in
the user's browser with no round-trip. Either approach yields the
same developer experience; the WASM version is what goes on
cure-lang.org's docs pages as inline executable snippets.

## Trying it out

Visit [`/playground`](/playground) and edit the default snippet.
Every keystroke re-parses the source; syntactically valid Cure shows
up coloured by its token classes (keywords, strings, operators,
literals, comments, types).

## Related

- [REPL](/repl) -- the local raw-mode cousin with the same
  highlighter.
- [Tooling](/tooling) -- the broader ecosystem around
  `cure check` / `cure fmt` / `cure doctor`.
- [Roadmap](/roadmap) -- what else lands in v0.27 / v0.28.
