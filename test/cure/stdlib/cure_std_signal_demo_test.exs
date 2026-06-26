defmodule Cure.Stdlib.SignalSensorDemoTest do
  @moduledoc """
  Closing integration evidence for `Std.Signal` (spec §1/§6): the worked
  `examples/signal_sensor.cure` pipeline (debounce -> drop_repeats -> foldp)
  driving the `examples/signal_alarm.cure` FSM, run on the host BEAM.

  `cure run` can only load a single module per file, so it cannot host a
  driver + a separately-compiled FSM. Instead we load both Cure modules into
  the VM via the compiler API (which is exactly what proves multi-module
  composition works) and run the driver, capturing its console line.
  """
  use ExUnit.Case, async: false
  import ExUnit.CaptureIO

  @driver :"Cure.SignalSensor"

  setup_all do
    Cure.Stdlib.Preload.preload(examples: false, kind: :all)

    # Load the Alarm FSM (compiles to Cure.FSM.Alarm) and then the driver.
    {:ok, _alarm} =
      Cure.Compiler.compile_and_load(File.read!("examples/signal_alarm.cure"),
        file: "examples/signal_alarm.cure"
      )

    {:ok, _driver} =
      Cure.Compiler.compile_and_load(File.read!("examples/signal_sensor.cure"),
        file: "examples/signal_sensor.cure"
      )

    :ok
  end

  test "the sensor pipeline trips then clears the Alarm FSM and reports it" do
    out = capture_io(fn -> assert @driver.run() == :ok end)
    # 60 (>=50) debounced+deduped trips the alarm once; 10 (<50) clears it.
    assert out =~ "SIGNAL demo: alarms=1 final=normal"
  end
end
