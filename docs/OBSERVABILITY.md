# Observability

v0.27.0 introduces three complementary observability surfaces for
running Cure applications: the `Cure.OTel` span bridge, the
`cure top` snapshot tool, and the `cure trace` typed tracer.

## Cure.OTel

`Cure.OTel` is an OpenTelemetry-compatible span emitter on top of
`Cure.Pipeline.Events`. It is started explicitly from an
application's `on_start` callback:

```elixir
Cure.OTel.start(
  exporter: &MyApp.Exporter.record/1,
  service_name: "my_app",
  sample_ratio: 1.0
)
```

When started, the bridge subscribes to every stage of the pipeline
event registry (`:lexer`, `:parser`, `:type_checker`, `:codegen`,
`:fsm_verifier`, `:sup_verifier`, `:app_verifier`, `:registry`) and
re-emits each event as a span.

Library code can also open manual spans through `Cure.OTel.span/3`:

```elixir
Cure.OTel.span("cure.actor.send", %{"inbox" => "Ping.Pong"}, fn ->
  pid |> send(message)
end)
```

Nested spans share a trace id and chain through `:parent_span_id`.
`Cure.OTel.inject_ctx/1` / `extract_ctx/1` propagate the span chain
across process boundaries -- typically inside the metadata carried
alongside a Melquiades Operator `<-|` message.

If `opentelemetry_api` is on the load path, spans are forwarded
there. Otherwise, the bundled `Cure.OTel.MemoryExporter` captures
every span in a public ETS table (`:cure_otel_spans`) usable from
tests and from the REPL via `:all/0`, `:flush/0`, `:count/0`.

## cure top

`cure top` prints a point-in-time snapshot of every running
supervisor, actor, and FSM:

```sh
mix cure.top           # or `cure top` when the escript is installed
watch -n1 mix cure.top # low-tech live view
```

Output:

```text
cure top  2026-04-21T15:20:00Z              procs=85  reductions=12345
Supervisors (1)
  - Cure.Sup.Atelier.Root  (2 children)
Actors (2)
  - painter_1 (Cure.Actor.Painter)  mbox=0  mem=9184  reds=301
  - curator_1 (Cure.Actor.Curator)  mbox=0  mem=9032  reds=212
FSMs (1)
  - exhibit_1 (Cure.FSM.Exhibit)  state=Closed  events=0  uptime_ms=42
```

Pair with `watch`, `entr`, or `keep` for a refresh-every-N-seconds
experience. The snapshot API (`Cure.Observe.Top.snapshot/0` and
`render/2`) is also consumable from code or from a Livebook.

## cure trace

`cure trace` attaches a typed tracer to a single `Module.fun/arity`
triple:

```sh
mix cure.trace Cure.Std.List.map/2 --duration 10
```

Every call and return is formatted through `inspect/2` and, when a
compile-time signature is known, annotated with the Cure type of
each argument and the declared effect set:

```text
call #PID<0.212.0> Cure.Std.List.map/2([1, 2, 3] : List(Int), #Function<...>)  [pure]
return #PID<0.212.0> Cure.Std.List.map/2 -> [2, 4, 6] : List(Int)
```

Signatures are stored in `Cure.Observe.Trace.Registry`, an ETS
table the type checker can populate during a project compile. Calls
whose signature is absent fall back to plain `inspect/2`.

## See also

- `examples/cure_atelier/` -- end-to-end exercise of all three
  surfaces plus the v0.27.0 stdlib and temporal checker.
- [`docs/TEMPORAL.md`](TEMPORAL.md) and [`docs/PROTOCOL.md`](PROTOCOL.md)
  for the verification side of the v0.27.0 toolkit.
