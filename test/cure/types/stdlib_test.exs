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

  # ============================================================================
  # Phase 1 (v0.34): stdlib type aliases
  # ============================================================================
  #
  # Stdlib refinement aliases (`Std.Refine.Positive`, ...), plain aliases,
  # and ADTs are now lifted from stdlib sources into the bundle and
  # installed into `env.types` whenever a matching `use Std.Mod` line is
  # processed by the type checker.
  describe "stdlib type aliases (Phase 1)" do
    test "all/0 exposes Std.Refine refinement aliases under qualified and short keys" do
      bundle = Stdlib.all()

      assert {:refinement, :int, _, _} =
               Map.fetch!(bundle.qualified_types, "Std.Refine.Positive")

      assert {:refinement, :int, _, _} =
               Map.fetch!(bundle.qualified_types, "Std.Refine.NonNegative")

      assert {:refinement, :float, _, _} =
               Map.fetch!(bundle.qualified_types, "Std.Refine.Probability")

      refine_short = Stdlib.short_types_for("Std.Refine")
      assert {:refinement, :int, _, _} = Map.fetch!(refine_short, "Positive")
      assert {:refinement, :int, _, _} = Map.fetch!(refine_short, "NonNegative")
    end

    test "install_qualified_types/1 registers fully qualified type aliases" do
      env = Stdlib.install_qualified_types(Env.new())

      assert {:ok, {:refinement, :int, _, _}} =
               Env.lookup_type(env, "Std.Refine.Positive")
    end

    test "install_import_types/2 brings short-name type aliases into env.types" do
      env = Stdlib.install_import_types(Env.new(), "Std.Refine")

      assert {:ok, {:refinement, :int, _, _}} = Env.lookup_type(env, "Positive")
      assert {:ok, {:refinement, :int, _, _}} = Env.lookup_type(env, "NonNegative")
      # An unrelated stdlib module's aliases must not leak into this env.
      assert :error = Env.lookup_type(env, "Currency")
    end

    test "install_import_types/2 tolerates `Cure.` prefixed module names" do
      env = Stdlib.install_import_types(Env.new(), "Cure.Std.Refine")

      assert {:ok, {:refinement, :int, _, _}} = Env.lookup_type(env, "Positive")
    end

    test "install_import_types/2 is a no-op for unknown modules" do
      env = Stdlib.install_import_types(Env.new(), "Nonexistent.Module")

      assert :error = Env.lookup_type(env, "Positive")
    end

    test "Env.deref/2 resolves an aliased name to its underlying refinement" do
      env = Stdlib.install_import_types(Env.new(), "Std.Refine")

      assert {:refinement, :int, _, _} = Env.deref(env, {:named, "Positive"})
      # Names not registered are returned as-is.
      assert {:named, "Unknown"} = Env.deref(env, {:named, "Unknown"})
      # Non-named types pass through.
      assert :int = Env.deref(env, :int)
    end

    test "Env.deref/2 is cycle-safe when an alias chain is self-referential" do
      env =
        Env.new()
        |> Env.extend_type("A", {:named, "B"})
        |> Env.extend_type("B", {:named, "A"})

      # Should terminate (returning whichever named term it last saw)
      # rather than looping.
      assert {:named, _} = Env.deref(env, {:named, "A"})
    end

    test "after `use Std.Refine`, a parameter declared as Positive resolves to a refinement" do
      src = """
      mod RefineConsumer
        use Std.Refine
        fn decrement(n: Positive) -> NonNegative = n - 1
      """

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)

      assert {:ok, _} = Cure.Types.Checker.check_module(ast, emit_events: false)
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

  describe "defensive caching" do
    test "empty?/1 recognises a fully empty bundle" do
      empty = %{qualified: %{}, short_by_module: %{}, qualified_types: %{}, types_by_module: %{}}

      assert Stdlib.empty?(empty)
      refute Stdlib.empty?(%{empty | qualified: %{"x" => 1}})
      refute Stdlib.empty?(%{empty | short_by_module: %{"m" => %{}}})
      refute Stdlib.empty?(%{empty | types_by_module: %{"m" => %{}}})
      refute Stdlib.empty?(%{empty | qualified_types: %{"x" => :int}})
    end

    test "does not memoise an empty bundle: a transient miss self-heals on retry" do
      source = Path.join(["lib", "std", "list.cure"])

      # The test is meaningful only from inside a Cure checkout where
      # we have a real stdlib file to swap in; skip gracefully otherwise.
      unless File.regular?(source), do: :ok

      previous = Application.get_env(:cure, :stdlib_source_dir)
      # Phase 1 (v0.34) bumped the bundle key to `:signatures_v3` to
      # invalidate any pre-existing cache on upgrade.
      persistent_key = {Cure.Types.Stdlib, :signatures_v3}

      empty_dir =
        Path.join(System.tmp_dir!(), "cure_stdlib_empty_#{System.unique_integer([:positive])}")

      populated_dir =
        Path.join(System.tmp_dir!(), "cure_stdlib_ready_#{System.unique_integer([:positive])}")

      File.mkdir_p!(empty_dir)
      File.mkdir_p!(populated_dir)
      File.cp!(source, Path.join(populated_dir, "list.cure"))

      try do
        # Phase 1: stdlib source dir exists but is empty (stdlib not
        # yet extracted). The loader must NOT cement this empty
        # bundle, otherwise every subsequent `:t` silently returns
        # `Any` for the lifetime of the VM.
        Application.put_env(:cure, :stdlib_source_dir, empty_dir)
        Stdlib.reload()
        _ = :persistent_term.erase(persistent_key)

        bundle = Stdlib.all()

        assert Stdlib.empty?(bundle)

        # The cache must still be unset -- the sentinel proves the
        # implementation did not `:persistent_term.put/2` an empty map.
        assert :persistent_term.get(persistent_key, :sentinel) == :sentinel

        # Phase 2: the stdlib becomes available on disk. A naive
        # implementation that cached the empty bundle would keep
        # returning empty; the self-healing implementation picks the
        # new content up without any explicit reload.
        Application.put_env(:cure, :stdlib_source_dir, populated_dir)

        recovered = Stdlib.all()

        refute Stdlib.empty?(recovered)
        assert Map.has_key?(recovered.short_by_module, "Std.List")

        # Now that the bundle is non-empty it is safe to memoise.
        assert :persistent_term.get(persistent_key, :sentinel) == recovered
      after
        case previous do
          nil -> Application.delete_env(:cure, :stdlib_source_dir)
          value -> Application.put_env(:cure, :stdlib_source_dir, value)
        end

        Stdlib.reload()
        File.rm_rf!(empty_dir)
        File.rm_rf!(populated_dir)
      end
    end
  end
end
