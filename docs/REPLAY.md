# @record and cure replay

Time-travel for FSMs landed in **v0.28.0**. Annotate any `fsm`
container with `@record` to journal every successful transition to
disk, then use `cure replay` to replay the recorded event sequence
against a fresh process -- stepping through it one event at a time
if you like.

## The `@record` annotation

Add `@record` immediately before an `fsm` container:

```
@record
fsm Turnstile
  Locked --coin--> Unlocked
  Unlocked --push--> Locked
```

When the container is compiled in callback mode (an `on_transition`
block is present, or `@record` triggers it), the generated
`GenServer` injects a call to `Cure.Observe.Journal.record/4` after
every successful state transition:

```elixir
if @record_transitions do
  Cure.Observe.Journal.record(self(), state.current, event, actual_next)
end
```

Simple-mode FSMs (no `on_transition` block) do not currently support
`@record`; the annotation is silently ignored. This will be extended
in a future release.

## The journal

`Cure.Observe.Journal` uses a named ETS table (`:cure_journal`) with
`write_concurrency: true` so any number of annotated processes can
write without contention.

Each journal entry is a 5-tuple:

```
{actor_id, state_before, event, state_after, timestamp_us}
```

- `actor_id`     -- `self()` from the recording process (a PID)
- `state_before` -- FSM state atom before the transition
- `event`        -- event atom that triggered the transition
- `state_after`  -- FSM state atom after the transition
- `timestamp_us` -- `:erlang.monotonic_time(:microsecond)` at recording time

### Flushing to disk

```elixir
{:ok, path} = Cure.Observe.Journal.flush(pid)
# => {:ok, ".cure-trace/3c2f1a...journal"}
```

Journal entries for `pid` are serialised as Erlang terms and written
to `.cure-trace/<hex_pid>.journal`. The hex filename is the
`Base.encode16` of `:erlang.term_to_binary(pid)`.

You can also call `flush/1` from a process monitor `DOWN` handler or
an OTP `terminate/2` callback to persist the trace before the
process exits.

### Inspecting in-memory entries

```elixir
Cure.Observe.Journal.entries()           # all entries
Cure.Observe.Journal.entries(pid)        # entries for one actor
Cure.Observe.Journal.clear()             # wipe all entries
```

## `cure replay`

```bash
cure replay <path.journal> [options]
```

Loads the journal file, prints the trace, and optionally replays the
event sequence against a live FSM module.

### Options

- `--module <Name>` / `-m <Name>` -- the FSM module atom to replay
  against. The module must be loaded; compile the project first with
  `cure compile` or `mix compile`.
- `--step` / `-s` -- pause after each event and wait for `[Enter]`
  before proceeding. Type `q` and `Enter` to quit early.
- `--no-print` -- suppress the trace table (only useful with
  `--module`).

### Example

```bash
cure replay .cure-trace/abc123.journal --module Cure.FSM.Turnstile
```

```text
Loaded 4 journal entries from .cure-trace/abc123.journal

Trace:
[  1] locked        --coin-------->  unlocked       (ok)
[  2] unlocked      --push-------->  locked         (ok)
[  3] locked        --coin-------->  unlocked       (ok)
[  4] unlocked      --push-------->  locked         (ok)

Replaying against Cure.FSM.Turnstile...
Replay complete: 4 ok, 0 warnings.
```

### Step mode

```bash
cure replay .cure-trace/abc123.journal \
  --module Cure.FSM.Turnstile --step
```

```text
[  1] locked        --coin-------->  unlocked       (ok)
  [Enter to continue, q to quit]
[  2] unlocked      --push-------->  locked         (ok)
  [Enter to continue, q to quit] q
Replay quit early.
```

### Without `--module`

When `--module` is omitted the trace table is printed but no live
replay is performed. Useful for inspection when the compiled module
is not available:

```bash
cure replay .cure-trace/abc123.journal
```

## Programmatic API

```elixir
# Load
{:ok, entries} = Cure.Observe.Journal.load(".cure-trace/abc123.journal")

# Print without replaying
Cure.Observe.Replay.print_trace(entries)

# Auto replay
{:ok, results} = Cure.Observe.Replay.replay(MyFsm, entries)

# Step replay with callback
{:ok, results} = Cure.Observe.Replay.replay(MyFsm, entries,
  step: true,
  on_event: fn n, from, event, to, outcome ->
    IO.puts("Event #{n}: #{from} --#{event}--> #{to} (#{outcome})")
  end
)
```

`replay/3` returns `{:ok, results}` where each element is
`{state_before, event, state_after, :ok | {:error, reason}}`, or
`{:ok, :quit}` if the user quit early in step mode.

## Mix task

```bash
mix cure.replay .cure-trace/abc123.journal
mix cure.replay .cure-trace/abc123.journal --module MyFsm --step
```

`mix cure.replay` accepts the same flags as the `cure replay` escript
subcommand.

## Related

- [`docs/OBSERVABILITY.md`](OBSERVABILITY.md) -- `cure top` and
  `cure trace`.
- [`docs/BLESS.md`](BLESS.md) -- `cure bless` type-error assistant.
- [`docs/FSM_GUIDE.md`](FSM_GUIDE.md) -- FSM containers, callback
  mode, and lifecycle hooks.
