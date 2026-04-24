defmodule Cure.Stdlib.PreloadTest do
  use ExUnit.Case, async: true

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
  end
end
