defmodule Cure.OTelTest do
  use ExUnit.Case, async: false

  alias Cure.OTel
  alias Cure.OTel.MemoryExporter
  alias Cure.Pipeline.Events

  setup do
    # Each test starts from a clean slate. The bridge is `name: __MODULE__`,
    # so stopping it here is safe even when no test has started it yet.
    :ok = OTel.stop()
    MemoryExporter.reset()
    OTel.clear_ctx()

    on_exit(fn ->
      :ok = OTel.stop()
      MemoryExporter.reset()
    end)

    :ok
  end

  describe "start/1 and running?/0" do
    test "is idempotent" do
      assert {:ok, pid} = OTel.start()
      assert {:ok, ^pid} = OTel.start()
      assert OTel.running?()
    end

    test "no-op when not running" do
      refute OTel.running?()
      # span/3 must simply run the fun
      assert OTel.span("x", %{}, fn -> 42 end) == 42
      assert MemoryExporter.count() == 0
    end
  end

  describe "pipeline-event span emission" do
    test "each emitted event becomes one span" do
      {:ok, _} = OTel.start(exporter: &MemoryExporter.record/1, service_name: "cure-test")
      # Let the bridge subscribe before we start emitting.
      _ = :sys.get_state(OTel)

      Events.emit(:type_checker, :function_checked, %{arity: 2}, Events.meta("foo.cure", 10))

      # Wait for the bridge to process the message.
      _ = :sys.get_state(OTel)

      assert [span] = MemoryExporter.all()
      assert span.name == "cure.type_checker.function_checked"
      assert span.attributes["cure.file"] == "foo.cure"
      assert span.attributes["cure.line"] == 10
      assert span.attributes["service.name"] == "cure-test"
      assert span.status == :ok
    end

    test "events matching an error-tag mark the span :error" do
      {:ok, _} = OTel.start(exporter: &MemoryExporter.record/1)
      _ = :sys.get_state(OTel)

      Events.emit(:parser, :parse_error, %{reason: :bad_token}, Events.meta("bad.cure", 3))
      _ = :sys.get_state(OTel)

      assert [span] = MemoryExporter.all()
      assert span.status == :error
    end
  end

  describe "manual span/3" do
    test "records one span, preserving return value" do
      {:ok, _} = OTel.start(exporter: &MemoryExporter.record/1)
      _ = :sys.get_state(OTel)

      result =
        OTel.span("cure.actor.send", %{"actor.inbox" => "ping"}, fn ->
          42
        end)

      _ = :sys.get_state(OTel)

      assert result == 42

      assert [%{name: "cure.actor.send", attributes: %{"actor.inbox" => "ping"}, status: :ok}] =
               MemoryExporter.all()
    end

    test "captures exceptions as :error spans and re-raises" do
      {:ok, _} = OTel.start(exporter: &MemoryExporter.record/1)
      _ = :sys.get_state(OTel)

      assert_raise RuntimeError, "boom", fn ->
        OTel.span("cure.actor.send", %{}, fn -> raise "boom" end)
      end

      _ = :sys.get_state(OTel)

      assert [%{status: :error}] = MemoryExporter.all()
    end

    test "nested spans share a trace id and chain via parent_span_id" do
      {:ok, _} = OTel.start(exporter: &MemoryExporter.record/1)
      _ = :sys.get_state(OTel)

      OTel.span("outer", %{}, fn ->
        OTel.span("inner", %{}, fn -> :ok end)
      end)

      _ = :sys.get_state(OTel)

      spans = MemoryExporter.all()
      assert length(spans) == 2

      inner = Enum.find(spans, &(&1.name == "inner"))
      outer = Enum.find(spans, &(&1.name == "outer"))

      assert inner.trace_id == outer.trace_id
      assert inner.parent_span_id == outer.span_id
      assert outer.parent_span_id == nil
    end
  end

  describe "cross-process context" do
    test "inject_ctx + extract_ctx re-seeds the span chain" do
      {:ok, _} = OTel.start(exporter: &MemoryExporter.record/1)
      _ = :sys.get_state(OTel)

      parent = self()

      OTel.span("producer", %{}, fn ->
        ctx = OTel.inject_ctx()

        pid =
          spawn(fn ->
            OTel.extract_ctx(ctx)

            OTel.span("consumer", %{}, fn ->
              send(parent, :done)
            end)
          end)

        ref = Process.monitor(pid)
        assert_receive :done, 500
        assert_receive {:DOWN, ^ref, :process, _, _}, 500
      end)

      _ = :sys.get_state(OTel)

      spans = MemoryExporter.all()
      producer = Enum.find(spans, &(&1.name == "producer"))
      consumer = Enum.find(spans, &(&1.name == "consumer"))

      assert producer.trace_id == consumer.trace_id
      assert consumer.parent_span_id == producer.span_id
    end

    test "inject_ctx returns :none when no span is active" do
      {:ok, _} = OTel.start(exporter: &MemoryExporter.record/1)
      assert OTel.inject_ctx() == :none
    end
  end

  describe "sampling" do
    test "sample_ratio: 0.0 drops every span" do
      {:ok, _} =
        OTel.start(exporter: &MemoryExporter.record/1, sample_ratio: 0.0)

      _ = :sys.get_state(OTel)

      OTel.span("sampled_out", %{}, fn -> :ok end)

      # Drain the cast queue.
      _ = :sys.get_state(OTel)

      assert MemoryExporter.count() == 0
    end
  end
end
