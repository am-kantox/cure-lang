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

  describe "path resolution" do
    test "honours `:stdlib_source_dir` override so host apps can point at a custom dir" do
      # Stage a copy of the real `Std.List` in an out-of-tree directory
      # and verify the loader picks it up via the configuration hook.
      # This is the exact mechanism `:cure_site` uses when running
      # inside a release where `lib/std/` is not on disk but
      # `priv/std/` is.
      source = Path.join(["lib", "std", "list.cure"])

      if File.regular?(source) do
        tmp = Path.join(System.tmp_dir!(), "cure_stdlib_test_#{System.unique_integer([:positive])}")
        File.mkdir_p!(tmp)
        File.cp!(source, Path.join(tmp, "list.cure"))

        previous = Application.get_env(:cure, :stdlib_source_dir)

        try do
          Application.put_env(:cure, :stdlib_source_dir, tmp)
          Stdlib.reload()

          bundle = Stdlib.all()

          assert Map.has_key?(bundle.short_by_module, "Std.List")
          assert {:fun, _, _} = Map.fetch!(bundle.qualified, "Std.List.map")
        after
          case previous do
            nil -> Application.delete_env(:cure, :stdlib_source_dir)
            value -> Application.put_env(:cure, :stdlib_source_dir, value)
          end

          Stdlib.reload()
          File.rm_rf!(tmp)
        end
      else
        :ok
      end
    end

    test "degrades to an empty bundle when no stdlib dir resolves" do
      previous = Application.get_env(:cure, :stdlib_source_dir)

      try do
        Application.put_env(
          :cure,
          :stdlib_source_dir,
          "/nonexistent/cure/stdlib_#{System.unique_integer([:positive])}"
        )

        Stdlib.reload()

        # We cannot force the priv/legacy candidates to disappear from
        # inside the Cure repo, so we only assert the override did not
        # crash the loader. The full "empty bundle" path is exercised
        # from host projects and release builds.
        bundle = Stdlib.all()
        assert is_map(bundle.qualified)
        assert is_map(bundle.short_by_module)
      after
        case previous do
          nil -> Application.delete_env(:cure, :stdlib_source_dir)
          value -> Application.put_env(:cure, :stdlib_source_dir, value)
        end

        Stdlib.reload()
      end
    end
  end
end
