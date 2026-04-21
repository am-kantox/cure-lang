defmodule Cure.Observe.TopTest do
  use ExUnit.Case, async: false

  alias Cure.Observe.Top

  describe "snapshot/0" do
    test "returns a map with the expected top-level keys" do
      snap = Top.snapshot()
      assert %{at: _, vm: _, supervisors: _, actors: _, fsms: _} = snap
      assert is_list(snap.supervisors)
      assert is_list(snap.actors)
      assert is_list(snap.fsms)
    end

    test "reports the process count and reductions" do
      snap = Top.snapshot()
      assert is_integer(snap.vm.process_count)
      assert snap.vm.process_count > 0
      assert is_integer(snap.vm.reductions)
    end
  end

  describe "render/2" do
    test "includes the cure-top banner, section headers, and empty placeholders" do
      out = Top.snapshot() |> Top.render(width: 80)

      assert out =~ "cure top"
      assert out =~ "Supervisors"
      assert out =~ "Actors"
      assert out =~ "FSMs"
    end
  end
end

defmodule Cure.Observe.TraceTest do
  use ExUnit.Case, async: false

  alias Cure.Observe.Trace

  setup do
    on_exit(fn -> Trace.stop() end)
    :ok
  end

  describe "signature registry" do
    test "register + lookup round-trip" do
      Trace.register_signature({Foo, :bar, 2}, ["Int", "String"], "Bool", [:io])

      assert {:ok, %{params: ["Int", "String"], return: "Bool", effects: [:io]}} =
               Trace.lookup_signature({Foo, :bar, 2})
    end

    test "missing entries return :error" do
      assert :error = Trace.lookup_signature({Foo, :unknown, 42})
    end
  end
end
