# Cure for VS Code
Cure language support for Visual Studio Code.
This extension provides:
- Syntax highlighting via TextMate grammar.
- Language Server Protocol integration with the `cure` binary.
- Bracket matching, indentation rules, and comment toggling.
## Requirements
- The `cure` binary must be on your PATH (or set `cure.lsp.path`).
- Build it from the Cure repo with `mix escript.build`.
## Settings
- `cure.lsp.path` -- path to the Cure binary (default: `cure`).
- `cure.lsp.args` -- arguments passed to the binary (default: `["lsp"]`).
## Building
```bash
npm install
npm run compile
```
This produces `out/extension.js`. Press `F5` in VS Code to launch the
extension in a development host.
## Status
Scaffold released in Cure v0.17.0. Marketplace publication is deferred
to a later release; for now, package locally with `vsce package`.
## License
MIT.
