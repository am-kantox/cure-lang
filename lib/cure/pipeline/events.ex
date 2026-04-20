defmodule Cure.Pipeline.Events do
  @moduledoc """
  PubSub event system for the Cure compilation pipeline.

  Every stage of the compilation pipeline (lexer, parser, type checker, codegen,
  FSM verifier) emits structured events through this module. External tools such
  as LSPs, profilers, debuggers, and IDE plugins can subscribe to these events
  to observe compilation in real time.

  ## Event Structure

  Events are 4-tuples: `{stage, event_type, payload, metadata}`

  - `stage` -- the pipeline stage (`:lexer`, `:parser`, `:type_checker`, `:codegen`, `:fsm_verifier`)
  - `event_type` -- stage-specific atom (e.g. `:token_produced`, `:node_parsed`, `:error`)
  - `payload` -- the data (token, AST node, type, error struct, etc.)
  - `metadata` -- `%{file: String.t(), line: pos_integer(), timestamp: integer()}`

  ## Subscribing

      # Subscribe to all events from the lexer
      Cure.Pipeline.Events.subscribe(:lexer)

      # Subscribe only to errors from the parser
      Cure.Pipeline.Events.subscribe(:parser, :error)

  ## Receiving Events

  Events are delivered as standard Erlang messages:

      receive do
        {Cure.Pipeline.Events, :lexer, :token_produced, token, meta} ->
          IO.inspect(token)
      end

  ## Emitting (used internally by pipeline stages)

      Cure.Pipeline.Events.emit(:lexer, :token_produced, token, %{file: "foo.cure", line: 1, timestamp: ...})
  """

  # `:registry` covers out-of-band lifecycle events from the package
  # registry and transparency log; every other stage maps to one of the
  # compilation pipeline phases.
  @type stage :: :lexer | :parser | :type_checker | :codegen | :fsm_verifier | :registry
  @type event_type :: atom()
  @type metadata :: %{file: String.t(), line: pos_integer(), timestamp: integer()}

  @registry Cure.Pipeline.Events.Registry

  @doc """
  Subscribe the calling process to all events from the given pipeline `stage`.

  Returns `:ok` on success.
  """
  @spec subscribe(stage()) :: :ok
  def subscribe(stage) when is_atom(stage) do
    {:ok, _} = Registry.register(@registry, stage, :all)
    :ok
  end

  @doc """
  Subscribe the calling process to events of a specific `event_type` from `stage`.

  Only events matching both `stage` and `event_type` will be delivered.
  """
  @spec subscribe(stage(), event_type()) :: :ok
  def subscribe(stage, event_type) when is_atom(stage) and is_atom(event_type) do
    {:ok, _} = Registry.register(@registry, stage, event_type)
    :ok
  end

  @doc """
  Emit a pipeline event. Called internally by pipeline stages.

  Dispatches the event to all subscribers of `stage`. Subscribers registered
  for a specific `event_type` will only receive matching events.

  The message delivered to subscribers is:

      {Cure.Pipeline.Events, stage, event_type, payload, metadata}
  """
  @spec emit(stage(), event_type(), term(), metadata() | keyword()) :: :ok
  def emit(stage, event_type, payload, metadata) when is_list(metadata) do
    metadata = metadata |> Map.new() |> Map.take([:file, :line, :timestamp])
    emit(stage, event_type, payload, metadata)
  end

  def emit(stage, event_type, payload, %{} = metadata) when is_atom(stage) and is_atom(event_type) do
    metadata =
      metadata
      |> Map.put_new(:file, "nofile")
      |> Map.put_new(:line, 1)
      |> Map.put_new(:timestamp, DateTime.utc_now() |> DateTime.to_unix(:millisecond))

    message = {__MODULE__, stage, event_type, payload, metadata}

    Registry.dispatch(@registry, stage, fn entries ->
      for {pid, filter} <- entries do
        if filter == :all or filter == event_type do
          send(pid, message)
        end
      end
    end)

    :ok
  end

  @doc """
  Build a metadata map for event emission.

  Convenience helper used by pipeline stages to construct the metadata
  argument for `emit/4`.
  """
  @spec meta(String.t(), pos_integer()) :: metadata()
  def meta(file, line) when is_binary(file) and is_integer(line) do
    %{file: file, line: line, timestamp: System.monotonic_time(:microsecond)}
  end
end
