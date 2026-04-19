# cure_brainloop

Reference example project for Cure v0.23.0: a toy expression-language
interpreter whose REPL is driven by a Cure-defined FSM.

`cure_brainloop` deliberately exercises every distinguishing Cure
feature inside one self-contained codebase:

- **ADT** with exhaustive matching -- `Expr = Num(Int) | Var(Atom) |
  BinOp(Op, Expr, Expr) | Let(Atom, Expr, Expr) | If(Expr, Expr, Expr)`
  (see `cure_src/ast.cure`).
- **Records** threaded through a recursive pass -- `Env{bindings: ...}`
  (see `cure_src/env.cure`).
- **Refinement types** for a push/pop-balanced stack
  (`cure_src/stack.cure`).
- **FSM, callback mode** for the REPL lifecycle
  (`cure_src/repl.cure`); includes a hard event (`quit!`), a soft
  event (`blank?`), and lifecycle callbacks.
- **OTP interop** via `CureBrainloop.Application`.
- **Stdlib usage** -- `Std.List`, `Std.Option`, `Std.Access`,
  `Std.Fsm`, and the new `Std.Json` for serialising the AST.
- **FFI** from Cure back to Elixir via `CureBrainloop.eval/1`.

## Running

```bash
# one-shot evaluation
mix run -e 'IO.inspect CureBrainloop.eval("let x = 2 in x * x + 1")'

# interactive REPL
mix escript.build
./cure_brainloop repl
```

## Tests

```bash
mix test
```

The test suite covers lexing, parsing, evaluation, and the REPL FSM
reachability.
