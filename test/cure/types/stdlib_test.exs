defmodule Cure.Types.StdlibTest do
  use ExUnit.Case, async: false

  alias Cure.Types.{Env, Stdlib}

  describe "all/0" do
    test "produces qualified and per-module short signatures" do
      bundle = Stdlib.all()

      assert is_map(bundle.qualified)
      assert is_map(bundle.short_by_module)

      assert "Std.List" in Map.keys(bundle.short_by_module)
      assert "Std.Math" in Map.keys(bundle.short_by_module)
    end

    test "Std.List.map resolves to the polymorphic signature" do
      bundle = Stdlib.all()

      assert {:fun, [{:list, {:type_var, "T"}}, {:fun, [{:type_var, "T"}], {:type_var, "U"}}],
              {:list, {:type_var, "U"}}} = Map.fetch!(bundle.qualified, "Std.List.map")
    end
  end

  describe "install_qualified/1" do
    test "registers every fully qualified name in the env" do
      env = Stdlib.install_qualified(Env.new())

      assert {:ok, {:fun, _, _}} = Env.lookup(env, "Std.List.map")
      assert {:ok, {:fun, _, _}} = Env.lookup(env, "Std.Math.abs")
    end
  end

  describe "install_import/2" do
    test "registers short names only for the requested module" do
      env = Stdlib.install_import(Env.new(), "Std.List")

      assert {:ok, {:fun, _, _}} = Env.lookup(env, "map")
      assert {:ok, {:fun, _, _}} = Env.lookup(env, "filter")
      # `product` is specific to `Std.List`; importing `Std.List` alone
      # should not surface short names from other stdlib modules.
      refute Map.has_key?(Stdlib.short_names_for("Std.Math"), "product")
    end

    test "tolerates `Cure.` prefixed module names" do
      env = Stdlib.install_import(Env.new(), "Cure.Std.List")

      assert {:ok, {:fun, _, _}} = Env.lookup(env, "map")
    end

    test "is a no-op for unknown modules" do
      env = Stdlib.install_import(Env.new(), "Nonexistent.Module")

      refute match?({:ok, {:fun, _, _}}, Env.lookup(env, "map"))
    end
  end
end
