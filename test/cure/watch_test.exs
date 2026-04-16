defmodule Cure.WatchTest do
  use ExUnit.Case, async: true

  alias Cure.Watch

  describe "snapshot/2" do
    setup do
      tmp = Path.join(System.tmp_dir!(), "cure_watch_test_#{:erlang.unique_integer([:positive])}")
      File.mkdir_p!(tmp)
      on_exit(fn -> File.rm_rf!(tmp) end)
      {:ok, tmp: tmp}
    end

    test "captures matching files with mtimes", %{tmp: tmp} do
      File.write!(Path.join(tmp, "a.cure"), "x")
      File.write!(Path.join(tmp, "b.cure"), "y")

      snap = Watch.snapshot(tmp, ["**/*.cure"])
      assert length(snap) == 2

      assert Enum.all?(snap, fn {p, _m} -> String.ends_with?(p, ".cure") end)
    end

    test "excludes non-matching files", %{tmp: tmp} do
      File.write!(Path.join(tmp, "a.cure"), "x")
      File.write!(Path.join(tmp, "b.txt"), "y")

      snap = Watch.snapshot(tmp, ["**/*.cure"])
      assert length(snap) == 1
    end

    test "returns sorted results", %{tmp: tmp} do
      File.write!(Path.join(tmp, "z.cure"), "x")
      File.write!(Path.join(tmp, "a.cure"), "y")

      snap = Watch.snapshot(tmp, ["**/*.cure"])
      [{p1, _}, {p2, _}] = snap
      assert p1 < p2
    end
  end

  describe "run_action/2" do
    test "unknown action prints an error" do
      out = ExUnit.CaptureIO.capture_io(:stderr, fn -> Watch.run_action(:bogus, ".") end)
      assert out =~ "unknown watch action"
    end
  end
end
