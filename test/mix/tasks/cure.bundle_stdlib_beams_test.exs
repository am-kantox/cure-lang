defmodule Mix.Tasks.Cure.BundleStdlibBeamsTest do
  use ExUnit.Case, async: true

  alias Mix.Tasks.Cure.BundleStdlibBeams

  describe "default_destination/0" do
    test "points at priv/ebin relative to the current project" do
      assert BundleStdlibBeams.default_destination() == Path.join(["priv", "ebin"])
    end
  end

  describe "module_name_from_source/1" do
    test "extracts the declared `mod` name" do
      src = make_tmp!()
      path = write_cure!(src, "list.cure", "mod Std.List\n  fn foo() -> Int = 1\n")

      assert {:ok, "Std.List"} = BundleStdlibBeams.module_name_from_source(path)
    after
      cleanup_tmps()
    end

    test "returns :unknown for a sourceless file" do
      assert :unknown = BundleStdlibBeams.module_name_from_source("/nonexistent/src.cure")
    end

    test "returns :unknown when no mod declaration is present" do
      src = make_tmp!()
      path = write_cure!(src, "bare.cure", "fn foo() -> Int = 1\n")

      assert :unknown = BundleStdlibBeams.module_name_from_source(path)
    after
      cleanup_tmps()
    end
  end

  describe "expected_beam_path/2" do
    test "prefixes with `Cure.` to match the codegen atom shape" do
      src = make_tmp!()
      path = write_cure!(src, "list.cure", "mod Std.List\n")

      assert {:ok, beam} = BundleStdlibBeams.expected_beam_path(path, "/tmp/out")
      assert beam == Path.join("/tmp/out", "Cure.Std.List.beam")
    after
      cleanup_tmps()
    end
  end

  describe "should_compile?/2" do
    test "returns true when the BEAM does not exist" do
      src = make_tmp!()
      path = write_cure!(src, "list.cure", "mod Std.List\n")

      assert BundleStdlibBeams.should_compile?(path, Path.join(src, "Cure.Std.List.beam"))
    after
      cleanup_tmps()
    end

    test "returns false when the BEAM is strictly newer than the source" do
      src = make_tmp!()
      dst = make_tmp!()
      source_path = write_cure!(src, "list.cure", "mod Std.List\n")
      beam_path = Path.join(dst, "Cure.Std.List.beam")
      File.write!(beam_path, "fake beam bytes")

      # Bump the beam mtime well past the source mtime so the gate says "skip".
      bump_mtime!(beam_path, 5)

      refute BundleStdlibBeams.should_compile?(source_path, beam_path)
    after
      cleanup_tmps()
    end

    test "returns true when the source has been updated" do
      src = make_tmp!()
      dst = make_tmp!()
      source_path = write_cure!(src, "list.cure", "mod Std.List\n")
      beam_path = Path.join(dst, "Cure.Std.List.beam")
      File.write!(beam_path, "fake beam bytes")

      # Source newer than beam.
      bump_mtime!(source_path, 5)

      assert BundleStdlibBeams.should_compile?(source_path, beam_path)
    after
      cleanup_tmps()
    end

    test "returns false when neither file exists" do
      refute BundleStdlibBeams.should_compile?(
               "/nonexistent/src.cure",
               "/nonexistent/dst.beam"
             )
    end
  end

  describe "bundle/2" do
    test "no-op when the source directory does not exist" do
      src = Path.join(System.tmp_dir!(), "cure_bundle_beams_missing_#{unique()}")
      dst = make_tmp!()

      assert {:ok, %{compiled: 0, skipped: 0, errors: 0}} = BundleStdlibBeams.bundle(src, dst)
      assert File.ls!(dst) == []
    after
      cleanup_tmps()
    end

    # We do not exercise the success path directly here because it
    # depends on `Cure.Compiler` being fully wired up, which the
    # integration-style tests in `test/cure/stdlib/preload_test.exs`
    # already cover end-to-end. Keeping this test module focused on
    # the pure helpers keeps it fast and isolated.
  end

  # ---------------------------------------------------------------------------

  defp make_tmp! do
    path = Path.join(System.tmp_dir!(), "cure_bundle_beams_test_#{unique()}")
    File.mkdir_p!(path)
    Process.put(:cleanup, [path | Process.get(:cleanup, [])])
    path
  end

  defp cleanup_tmps do
    Process.get(:cleanup, []) |> Enum.each(&File.rm_rf!/1)
    Process.put(:cleanup, [])
  end

  defp write_cure!(dir, name, contents) do
    path = Path.join(dir, name)
    File.write!(path, contents)
    path
  end

  defp bump_mtime!(path, offset_seconds) do
    {:ok, %File.Stat{mtime: mtime}} = File.stat(path, time: :posix)
    File.touch!(path, mtime + offset_seconds)
  end

  defp unique, do: System.unique_integer([:positive])
end
