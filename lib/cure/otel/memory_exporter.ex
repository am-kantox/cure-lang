defmodule Cure.OTel.MemoryExporter do
  @moduledoc """
  In-memory span exporter for `Cure.OTel` (v0.27.0).

  Spans are recorded into a public ETS table (`:cure_otel_spans`) so
  callers can inspect them after the fact. The table is created on
  first `start/0` and left alone if it already exists.

  Intended uses:

    - Test assertions against span shape and attributes
      (`test/cure/otel_test.exs`).
    - The `examples/cure_atelier/` showcase, which verifies that OTel
      spans are produced for every actor send.
    - Manual inspection from the REPL while debugging.

  Public API:

    - `start/0` -- create the ETS table if needed. Idempotent.
    - `record/1` -- append a span. Safe to call from any process.
    - `flush/0` -- return and clear every stored span.
    - `all/0` -- return every stored span without clearing.
    - `count/0` -- number of stored spans.
    - `reset/0` -- drop every stored span.
  """

  @table :cure_otel_spans

  @doc "Create the backing ETS table. Safe to call repeatedly."
  @spec start() :: :ok
  def start do
    case :ets.whereis(@table) do
      :undefined ->
        :ets.new(@table, [:ordered_set, :public, :named_table, {:write_concurrency, true}])
        :ok

      _ ->
        :ok
    end
  end

  @doc "Append a span to the backing table."
  @spec record(map()) :: :ok
  def record(%{name: _} = span) do
    start()
    key = {System.monotonic_time(:nanosecond), :erlang.unique_integer([:monotonic])}
    :ets.insert(@table, {key, span})
    :ok
  end

  def record(_), do: :ok

  @doc """
  Return every stored span in emission order and clear the table.
  """
  @spec flush() :: [map()]
  def flush do
    start()
    spans = all()
    :ets.delete_all_objects(@table)
    spans
  end

  @doc "Return every stored span in emission order."
  @spec all() :: [map()]
  def all do
    start()

    @table
    |> :ets.tab2list()
    |> Enum.sort_by(&elem(&1, 0))
    |> Enum.map(&elem(&1, 1))
  end

  @doc "Return the number of stored spans."
  @spec count() :: non_neg_integer()
  def count do
    start()
    :ets.info(@table, :size)
  end

  @doc "Remove every stored span."
  @spec reset() :: :ok
  def reset do
    start()
    :ets.delete_all_objects(@table)
    :ok
  end
end
