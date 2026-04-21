# cure_atelier

Showcase project for Cure v0.27.0 ("See Your System Breathe").

This example exercises every v0.27.0 surface in a single, self-
contained project:

- **`Std.CRDT.ORSet`** for the exhibit's tag set (so the curator and
  painter can add and remove tags concurrently without coordination).
- **`Std.Time.Instant`** for wall-clock timestamps on every curation
  event, exercised via the `:cure_std_time` runtime.
- **`Std.Regex`** for input validation of human-supplied titles.
- **`Cure.Protocol`** verifies a session-typed `Atelier.Gallery`
  protocol between `Painter` and `Curator` roles; the test suite
  asserts the happy path passes `Cure.Protocol.verify/1` and a
  deliberately broken variant surfaces `E056`.
- **`Cure.Temporal`** specifies liveness properties over an
  `Exhibit` FSM (`always eventually Open`, `never (Open and Closed)`)
  and exercises both passing and failing variants.
- **`Cure.OTel`** with the bundled `MemoryExporter` captures every
  actor send and FSM transition; the test suite asserts spans are
  produced end-to-end.
- **`Cure.Term.Hyperlink`** is exercised indirectly via the shared
  compiler error path.
- **`cure top`** and **`cure trace`** are runnable against the
  spawned actors -- see the `docs` section of the test output.

## Layout

```text
examples/cure_atelier/
  README.md           -- this file
  Cure.toml           -- project metadata
  mix.exs             -- Elixir harness
  cure_src/
    painter.cure      -- actor containing the painter role
    curator.cure      -- actor containing the curator role
  test/
    cure_atelier_test.exs   -- end-to-end suite
    test_helper.exs
```

## Running

```sh
mix deps.get
mix compile_cure      # compiles cure_src/*.cure into _build/cure/ebin
mix test              # runs the showcase suite
```

## Feature walk-through

Every `describe/2` block in `test/cure_atelier_test.exs` maps to one
v0.27.0 feature. Read the tests top-to-bottom for the most compact
tour of the release.
