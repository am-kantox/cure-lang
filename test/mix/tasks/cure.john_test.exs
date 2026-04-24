defmodule Mix.Tasks.Cure.JohnTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  alias Mix.Tasks.Cure.John, as: Task

  setup do
    tmp = Path.join(System.tmp_dir!(), "cure_john_task_#{:erlang.unique_integer([:positive])}")
    File.mkdir_p!(tmp)
    on_exit(fn -> File.rm_rf!(tmp) end)
    {:ok, root: tmp}
  end

  test "run/1 writes a rendered diagnostic to stdout", %{root: root} do
    output =
      capture_io(fn ->
        Task.run(["--no-ansi", "--no-banner", "--root", root])
      end)

    assert output =~ "## Cure"
    assert output =~ "## BEAM / OTP"
    assert output =~ "## Tooling"
  end

  test "run/1 accepts --width without crashing", %{root: root} do
    output =
      capture_io(fn ->
        Task.run(["--no-ansi", "--no-banner", "--width", "120", "--root", root])
      end)

    # The section separator at the footer is half the width (capped at 20).
    assert output =~ String.duplicate("-", 60)
  end
end
