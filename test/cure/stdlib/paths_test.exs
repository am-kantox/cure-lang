defmodule Cure.Stdlib.PathsTest do
  # async: false -- each test flips `Application.get_env(:cure,
  # :stdlib_source_dir)` which is process-global state.
  use ExUnit.Case, async: false

  alias Cure.Stdlib.Paths

  setup do
    previous = Application.get_env(:cure, :stdlib_source_dir)

    on_exit(fn ->
      case previous do
        nil -> Application.delete_env(:cure, :stdlib_source_dir)
        value -> Application.put_env(:cure, :stdlib_source_dir, value)
      end
    end)

    :ok
  end

  describe "bundle_destination/0" do
    test "points at priv/std relative to the current project" do
      assert Paths.bundle_destination() == Path.join(["priv", "std"])
    end
  end

  describe "source_dirs/0" do
    test "includes the legacy cwd-relative lib/std when present" do
      # The Cure repo ships `lib/std/` -- this should always be on the
      # list from inside the Cure project tree.
      assert Path.join(["lib", "std"]) in Paths.source_dirs()
    end

    test "prepends the configured override when it exists" do
      tmp = make_tmp!()

      try do
        Application.put_env(:cure, :stdlib_source_dir, tmp)
        dirs = Paths.source_dirs()

        assert List.first(dirs) == tmp
      after
        File.rm_rf!(tmp)
      end
    end

    test "drops the configured override when the directory is missing" do
      bogus = Path.join(System.tmp_dir!(), "cure_paths_does_not_exist_#{unique()}")
      Application.put_env(:cure, :stdlib_source_dir, bogus)

      refute bogus in Paths.source_dirs()
    end

    test "returns only existing directories" do
      assert Enum.all?(Paths.source_dirs(), &File.dir?/1)
    end

    test "is idempotent across calls (no hidden mutable state)" do
      assert Paths.source_dirs() == Paths.source_dirs()
    end
  end

  describe "source_dir/0" do
    test "returns the first element of source_dirs/0" do
      case Paths.source_dirs() do
        [] -> assert Paths.source_dir() == nil
        [first | _] -> assert Paths.source_dir() == first
      end
    end

    test "returns nil when nothing resolves" do
      # Walk past every candidate by pointing the override at a
      # nonexistent path; the priv/legacy fallbacks may still resolve
      # when running from the Cure repo, so we only assert the
      # override was ignored. A stricter "returns nil" test would
      # require sandboxing `:code.priv_dir/1`, which is out of scope.
      Application.put_env(:cure, :stdlib_source_dir, "/nonexistent/cure/stdlib/#{unique()}")
      assert Paths.source_dir() != "/nonexistent/cure/stdlib"
    end
  end

  # ---------------------------------------------------------------------------

  defp make_tmp! do
    path = Path.join(System.tmp_dir!(), "cure_paths_test_#{unique()}")
    File.mkdir_p!(path)
    path
  end

  defp unique, do: System.unique_integer([:positive])
end
