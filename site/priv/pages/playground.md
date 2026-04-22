%{
  title: "Playground",
  description: "The Cure Playground: live syntax highlighting, a real-time type-check panel, and a sandboxed evaluator -- all in the browser.",
  order: 13
}
---
The Cure Playground is an in-browser editor for exploring Cure without
installing anything locally. Visit [`/playground`](/playground) and
start typing. The LiveView updates three panels on every keystroke
(debounced at 150 ms):

1. **Syntax-highlighted preview** -- `Makeup.Lexers.CureLexer` colours
   keywords, types, operators, strings, and comments, the same way the
   REPL does.
2. **Type-check panel** -- the full bidirectional checker
   (`Cure.Types.Checker`) runs on the source and shows either a green
   "OK -- no type errors" or a formatted list of diagnostics with file
   and line numbers.
3. **Eval output** (on demand) -- hit the **Run** button to compile
   the source and call `main/0` in a sandboxed BEAM process. Return
   value and stdout appear inline.

## What shipped in v0.27.0

- Two-pane editor: source textarea on the left, Makeup-highlighted
  HTML preview on the right.
- 150 ms debounced LiveView updates.
- Tailwind-based layout.

## What shipped in v0.28.0

- **Live type-check panel** -- always-on, debounced. Powered by
  `Cure.Types.Checker.check_module/2` called directly from the
  LiveView.
- **Sandboxed evaluator** -- `CureSiteWeb.Eval` uses
  `:erlang.spawn_opt/2` with a 64 MB heap limit and a 2-second kill
  timer. User code cannot block the server. `main/0` return value and
  captured stdout are returned to the browser.

## What lands in v0.29

The WASM target -- compiling the pure compiler half to WASM via AtomVM
so docs pages can embed truly in-browser executable snippets with no
server round-trip -- is scheduled for v0.29.

## Trying it out

Visit [`/playground`](/playground) and edit the default snippet.
Syntax errors are highlighted as you type; type errors appear in the
type-check panel. Click **Run** to evaluate.

## Related

- [REPL](/repl) -- the local raw-mode cousin with the same
  highlighter.
- [Tooling](/tooling) -- the broader ecosystem around
  `cure check` / `cure fmt` / `cure bless`.
- [Roadmap](/roadmap) -- what's planned beyond v0.28.
