# cure_motif

A length-indexed step sequencer that makes **dependent types the star of the
show**. Where `cure_moneta` exercises refinement types on a business domain
(money) and `cure_forge` exercises the full OTP surface, `cure_motif` puts
**`Std.Vector`-backed length tracking**, a **typed `@record`-enabled FSM**, an
**actor relay over the Melquiades Operator**, and a **`Cure.Temporal` liveness
proof** together in one ~400-line project that also ships a runnable ASCII
piano-roll demo.

## Quick start

```bash
cd examples/cure_motif
mix deps.get
mix deps.compile cure            # one-time; builds the :cure parent dep
mix test
```

The `test` alias runs `compile_cure` first so every Cure container is live in
the VM by the time ExUnit starts.

## What the showcase exercises

Each bullet corresponds to at least one `describe/2` block in the test suite
at `test/cure_motif_test.exs`.

### Refinement types + SMT (`motif.cure:32`)

```cure
type Pitch        = {p: Int | p >= 0 and p <= 127}
type Velocity     = {v: Int | v >= 1 and v <= 127}
type Channel      = {c: Int | c >= 0 and c <= 15}
type Bpm          = {b: Int | b >= 20 and b <= 300}
type StepsPerBeat = {s: Int | s >= 1 and s <= 16}
type BarCount     = {n: Int | n >= 1 and n <= 64}
type RollReps     = {k: Int | k >= 2 and k <= 8}
```

Every MIDI-domain primitive is refinement-typed. Safe constructors (`note/2`,
`chord/3`, `roll/3`) take the refined types, so out-of-range literals fail
`cure check`, not at runtime.

### Length-indexed patterns (`motif.cure:99`)

A `Pattern` is a `Std.Vector` of `Step`s, and the length claim is observable
through `Std.Vector.length/1`:

```cure
fn concat(a: Tuple, b: Tuple) -> Tuple = Std.Vector.append(a, b)

fn repeat(p: Tuple, n: BarCount) -> Tuple = repeat_acc(p, n, empty_pattern())
```

The test suite defends the dependent claims directly:

```elixir
assert @motif.pattern_length(@motif.concat(a, b)) ==
         @motif.pattern_length(a) + @motif.pattern_length(b)

assert @motif.pattern_length(@motif.repeat(p, 4)) == 8
```

### ADTs with parameterised variants (`motif.cure:63`)

```cure
type Step =
  | Rest
  | Note(Int, Int)
  | Chord(Int, Int, Int)
  | Roll(Int, Int, Int)

type Event =
  | NoteOn(Int, Int, Int)
  | NoteOff(Int, Int)
  | Tick(Int)
```

`step_events/2` and `render/2` are total functions over `Step`. Exhaustiveness
is enforced by the checker; the renderer can never "forget" a new variant.

### @record-ready callback-mode FSM (`envelope.cure`)

```cure
@record
fsm Envelope with Int
  Silent   --note_on-->   Attack
  Attack   --peak-->      Sustain
  Sustain  --note_off-->  Release
  Release  --done-->      Silent
  *        --kill?-->     Silent

  @timer 25
  on_timer
    (:attack,  _) -> %[:transition, :peak, 0]
    (:release, _) -> %[:transition, :done, 0]
    (_, _)        -> :ok
  ...
```

Four states, four event kinds (`note_on`, `note_off`, the two auto-fired
`peak` and `done` transitions, and the wildcard soft `kill?`). The
`on_timer` callback drives `Attack -> Sustain` and `Release -> Silent`
without any caller intervention. `@record` is written exactly as
`docs/REPLAY.md` specifies; the current parser routes decorators through
`fn`/`rec` containers, so the compile-time auto-journal is the next wiring
step. Today the test suite exercises `Cure.Observe.Journal` and
`Cure.Observe.Replay` directly, which is the same pipeline the decorator
will eventually feed.

### Cure.Temporal liveness proofs

The Envelope's compiled transition table is fed straight into the LTL
bounded model checker:

```elixir
{:ok, f} = Cure.Temporal.Parser.parse_one("always (attack -> eventually sustain)")
assert {:ok, :holds} = Cure.Temporal.Checker.check(f, envelope_model())
```

Three liveness properties and one safety counter-example are all exercised
by `test/cure_motif_test.exs`:

- `always eventually silent`
- `always (attack -> eventually sustain)`
- `always (release -> eventually silent)`
- `never attack` (expected to fail, with `"attack"` in the counterexample trail)

### Typed actors + Melquiades Operator

Three actor containers, one per file:

- `clock.cure`     -- monotonic tick counter
- `sequencer.cure` -- single-event relay bumping a counter per tick
- `voice.cure`     -- tracks play/stop state for one voice

Each is compiled to `:"Cure.Actor.<Name>"` and supervised under the
`sup Motif.Orchestra` container in `orchestra.cure`. The sequencer's
`notify(%[:event, event])` call is the Elixir side of the Melquiades
Operator: the message lands in whichever process started the actor, which
is how `CureMotif.MidiOut` ends up with the full event log.

### Typed OTP application + release

`motif_app.cure` declares the `app CureMotif` container with `root = sup
Motif.Orchestra`, a full `env` map, and `on_start` / `on_stop` hooks. A
`cure release` of this project produces a bootable BEAM release under
`_build/cure/rel/cure_motif/`.

### ASCII piano-roll renderer (Elixir side)

`CureMotif.PianoRoll.render/1` turns the captured event log into the kind
of thing you can paste into a terminal and read at a glance:

```
     ||||||||||||||||
 67  ..........X.....
 64  ....X.......X...
 62  ..X...X.......X.
 60  X...X...X...X...
 57  ....X.......X...
```

This is what `CureMotif.Demo.run/0` prints (well, returns) end-to-end.

## Project layout

```text
examples/cure_motif/
  README.md                               -- this file
  Cure.toml                               -- [project] + [application] + [release]
  mix.exs                                 -- Elixir harness entry point
  .formatter.exs / .gitignore
  cure_src/
    motif.cure                            -- refinement types, ADTs, Pattern helpers, rendering
    envelope.cure                         -- @record-annotated callback-mode FSM
    voice.cure                            -- voice actor (per-note state tracker)
    sequencer.cure                        -- sequencer actor (single-event relay + counter)
    clock.cure                            -- clock actor (monotonic tick counter)
    orchestra.cure                        -- sup Motif.Orchestra (root supervisor)
    motif_app.cure                        -- app CureMotif (OTP application container)
  lib/
    cure_motif.ex                         -- public Elixir facade
    cure_motif/
      application.ex                      -- OTP Application callback
      midi_out.ex                         -- in-memory event sink (bounded log)
      piano_roll.ex                       -- ASCII piano-roll renderer
      demo.ex                             -- packaged end-to-end walkthrough
    mix/
      tasks/
        compile_cure.ex                   -- Mix.Tasks.CompileCure
  test/
    cure_motif_test.exs                   -- 42 cases across 12 describe blocks
    test_helper.exs
```

## Running the demo interactively

```bash
iex -S mix
```

```elixir
iex> {:ok, _} = Application.ensure_all_started(:cure_motif)
iex> Supervisor.which_children(CureMotif.sup_module())
[
  {:voice,     #PID<0.xxx.0>, :worker, [:"Cure.Actor.Voice"]},
  {:sequencer, #PID<0.xxx.0>, :worker, [:"Cure.Actor.Sequencer"]},
  {:clock,     #PID<0.xxx.0>, :worker, [:"Cure.Actor.Clock"]}
]

iex> %{roll: roll} = CureMotif.Demo.run()
iex> IO.puts(roll)
     ||||||||||||||||
 67  ..........X.....
 64  ....X.......X...
 62  ..X...X.......X.
 60  X...X...X...X...
 57  ....X.......X...
```

## Known limitations

- **`@record` parser plumbing.** The parser currently attaches decorators to
  `fn`, `local`, and `rec` containers only. `@record` on `fsm` is parsed as
  a standalone `:property` node, so it does not yet flip the
  `@record_transitions` bit in the generated FSM module. The journal and
  replay APIs still work; see the `@record journal + Replay` describe block
  for the workaround.
- **Cons patterns in actor/FSM callback clauses.** The Cure-to-Elixir AST
  translator in `Cure.FSM.Compiler.cure_ast_to_elixir/1` emits `[head | tail]`
  Cure patterns as Elixir `[head, tail]` fixed-length matches. The
  `Sequencer` actor is intentionally designed around a single-event
  `%[:emit, e]` message to sidestep this limitation; the Elixir facade does
  the list walking.

Both are shallow compiler fixes; neither affects the user-visible correctness
of the showcase once the fixes land.

## See also

- [`docs/TYPE_SYSTEM.md`](../../docs/TYPE_SYSTEM.md) -- bidirectional
  checking and refinement types
- [`docs/FSM_GUIDE.md`](../../docs/FSM_GUIDE.md) -- FSM containers,
  callback mode, lifecycle hooks
- [`docs/TEMPORAL.md`](../../docs/TEMPORAL.md) -- LTL temporal checker
- [`docs/REPLAY.md`](../../docs/REPLAY.md) -- `@record` and `cure replay`
- [`docs/SUPERVISION.md`](../../docs/SUPERVISION.md) -- `actor`, `sup`, and
  the Melquiades Operator
- [`docs/APP.md`](../../docs/APP.md) -- `app` containers and `cure release`
