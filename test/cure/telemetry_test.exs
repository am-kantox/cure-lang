defmodule Cure.TelemetryTest do
  use ExUnit.Case, async: false

  alias Cure.Telemetry

  test "start/0 is idempotent" do
    {:ok, pid1} = Telemetry.start()
    on_exit(fn -> Telemetry.stop() end)
    assert Process.alive?(pid1)

    case Telemetry.start() do
      {:error, {:already_started, ^pid1}} -> :ok
      {:ok, pid2} -> assert Process.alive?(pid2)
    end
  end

  test "stop/0 with no bridge returns :ok" do
    # Make sure no bridge running
    _ = Telemetry.stop()
    assert :ok = Telemetry.stop()
  end
end
