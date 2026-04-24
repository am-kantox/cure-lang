defmodule Cure.Stdlib.PreloadTest do
  # async: false -- the preload stanza mutates `:cure` application
  # env entries (`:stdlib_beam_dir`, `:stdlib_source_dir`) which are
  # process-global state.
  use ExUnit.Case, async: false

  alias Cure.Stdlib.Preload

  describe "known_groups/0" do
    test "returns the canonical list of stdlib groups" do
      groups = Preload.known_groups()

      assert :core in groups
      assert :collections in groups
      assert :text in groups
      assert :numeric in groups
      assert :system in groups
      assert :concurrency in groups
      assert :option in groups
      assert :test in groups
      assert :network in groups
    end
  end

  describe "module_groups/0" do
    test "is built at compile time from lib/std/*.cure" do
      groups = Preload.module_groups()

      assert is_map(groups)
      assert Map.get(groups, :"Cure.Std.Core") == :core
      assert Map.get(groups, :"Cure.Std.List") == :collections
      assert Map.get(groups, :"Cure.Std.Math") == :numeric
      assert Map.get(groups, :"Cure.Std.Http") == :network
      assert Map.get(groups, :"Cure.Std.Option") == :option
    end
  end

  describe "stdlib_modules/1" do
    test ":none returns the empty list (default)" do
      assert Preload.stdlib_modules() == []
      assert Preload.stdlib_modules(:none) == []
    end

    test ":all returns every known stdlib module" do
      mods = Preload.stdlib_modules(:all)

      # Sanity check a handful of modules we know must be present.
      for m <- [:"Cure.Std.Core", :"Cure.Std.List", :"Cure.Std.Math", :"Cure.Std.Http"] do
        assert m in mods
      end

      assert length(mods) == map_size(Preload.module_groups())
    end

    test ":core matches the modules explicitly described in the spec" do
      core = Preload.stdlib_modules(:core)

      # The user-facing spec requires these exact modules under :core.
      required = ~w(Core Equal Eq Ord Show Functor Refine)a

      for short <- required do
        module = String.to_atom("Cure.Std.#{short}")
        assert module in core, "expected #{inspect(module)} in :core"
      end

      refute :"Cure.Std.List" in core
      refute :"Cure.Std.Http" in core
    end

    test "a single-group atom filters to that group" do
      collections = Preload.stdlib_modules(:collections)
      assert :"Cure.Std.List" in collections
      assert :"Cure.Std.Map" in collections
      refute :"Cure.Std.Core" in collections
    end

    test "a list of groups unions their membership with no duplicates" do
      merged = Preload.stdlib_modules([:core, :option, :option])
      assert :"Cure.Std.Core" in merged
      assert :"Cure.Std.Option" in merged
      assert :"Cure.Std.Result" in merged
      assert merged == Enum.uniq(merged)
    end

    test "unknown kind atom raises ArgumentError" do
      assert_raise ArgumentError, fn -> Preload.stdlib_modules(:bogus) end
    end

    test "non-atom / non-list kind raises ArgumentError" do
      assert_raise ArgumentError, fn -> Preload.stdlib_modules("core") end
      assert_raise ArgumentError, fn -> Preload.stdlib_modules(42) end
    end

    test "unknown group inside a list raises ArgumentError" do
      assert_raise ArgumentError, fn -> Preload.stdlib_modules([:core, :bogus]) end
    end
  end

  describe "preload/1" do
    test ":none (default) returns :ok without touching the VM" do
      assert Preload.preload() == :ok
      assert Preload.preload(kind: :none) == :ok
    end

    test "kind: :all loads every known stdlib module" do
      assert Preload.preload(examples: false, kind: :all) == :ok

      # A representative sample should be loaded after the call.
      assert Code.ensure_loaded?(:"Cure.Std.Core")
      assert Code.ensure_loaded?(:"Cure.Std.List")
    end

    test "unknown kind raises ArgumentError" do
      assert_raise ArgumentError, fn -> Preload.preload(kind: :bogus) end
    end

    # Regression for the production Yeesh REPL: in a release,
    # `_build/cure/ebin` is absent and the bundled `priv/ebin/` is the
    # only place stdlib BEAMs live. The stanza below pretends `priv/ebin/`
    # is elsewhere on disk and asserts the preload picks it up.
    test "honours :stdlib_beam_dir app-env override" do
      tmp = make_tmp!()

      # Seed the tmp dir with a single real stdlib BEAM harvested from
      # the legacy build output (we expect the project's `mix compile`
      # to have produced them). If the source of truth isn't present
      # we skip -- the happy path below in `load_from_candidates` is
      # already exercised by `kind: :all` above.
      case staged_sample_beam() do
        {:ok, module, binary} ->
          File.write!(Path.join(tmp, "#{module}.beam"), binary)
          # Evict the module from the VM so we can observe the reload.
          :code.purge(module)
          :code.delete(module)

          previous = Application.get_env(:cure, :stdlib_beam_dir)
          Application.put_env(:cure, :stdlib_beam_dir, tmp)

          try do
            assert Preload.preload(kind: :all, source_jit: false) == :ok
            assert Code.ensure_loaded?(module)
          after
            case previous do
              nil -> Application.delete_env(:cure, :stdlib_beam_dir)
              value -> Application.put_env(:cure, :stdlib_beam_dir, value)
            end

            File.rm_rf!(tmp)
          end

        :skip ->
          File.rm_rf!(tmp)
          # Missing legacy BEAMs; nothing to assert against.
          :ok
      end
    end
  end

  describe "compile_missing_from_sources/1" do
    # `:source_jit` is opt-out, so a deployment carrying the .cure
    # sources but no BEAMs should still be usable after `preload/1`.
    test "recovers an unloaded module by compiling it from source" do
      module = :"Cure.Std.List"

      previous_beam = Application.get_env(:cure, :stdlib_beam_dir)
      # Point the BEAM lookup at a directory that has no `.beam` files
      # so the JIT path is guaranteed to fire.
      empty = make_tmp!()
      Application.put_env(:cure, :stdlib_beam_dir, empty)

      # Evict the module first. We rely on `priv/std/list.cure` being
      # bundled already (Mix.Tasks.Cure.BundleStdlib runs on every
      # compile).
      :code.purge(module)
      :code.delete(module)
      refute Code.ensure_loaded?(module)

      try do
        assert Preload.compile_missing_from_sources(:collections) == :ok
        assert Code.ensure_loaded?(module)
      after
        case previous_beam do
          nil -> Application.delete_env(:cure, :stdlib_beam_dir)
          value -> Application.put_env(:cure, :stdlib_beam_dir, value)
        end

        File.rm_rf!(empty)
      end
    end

    test "silently no-ops when neither BEAM nor source is reachable" do
      previous_beam = Application.get_env(:cure, :stdlib_beam_dir)
      previous_src = Application.get_env(:cure, :stdlib_source_dir)
      empty = make_tmp!()
      Application.put_env(:cure, :stdlib_beam_dir, empty)
      Application.put_env(:cure, :stdlib_source_dir, empty)

      try do
        # `:collections` selects several modules; none of them will
        # have a backing source in `empty`, but the call must succeed.
        assert Preload.compile_missing_from_sources(:collections) == :ok
      after
        case previous_beam do
          nil -> Application.delete_env(:cure, :stdlib_beam_dir)
          value -> Application.put_env(:cure, :stdlib_beam_dir, value)
        end

        case previous_src do
          nil -> Application.delete_env(:cure, :stdlib_source_dir)
          value -> Application.put_env(:cure, :stdlib_source_dir, value)
        end

        File.rm_rf!(empty)
      end
    end
  end

  # ---------------------------------------------------------------------------

  defp make_tmp! do
    path =
      Path.join(System.tmp_dir!(), "cure_preload_test_#{System.unique_integer([:positive])}")

    File.mkdir_p!(path)
    path
  end

  # Find any one compiled stdlib BEAM we can reuse for the
  # `:stdlib_beam_dir` override check. Returns `{:ok, module, binary}`
  # when a harvestable BEAM is available on disk, `:skip` otherwise.
  defp staged_sample_beam do
    ["_build/cure/ebin", Path.join(["priv", "ebin"])]
    |> Enum.find_value(:skip, fn dir ->
      case dir |> Path.join("Cure.Std.Core.beam") |> File.read() do
        {:ok, binary} -> {:ok, :"Cure.Std.Core", binary}
        _ -> nil
      end
    end)
  end
end
