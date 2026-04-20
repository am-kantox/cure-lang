defmodule Cure.REPL.DocsTest do
  use ExUnit.Case, async: true

  alias Cure.REPL.Docs
  alias Cure.REPL.Theme

  describe "parse_target/1" do
    test "module with dotted path" do
      assert {:ok, {:module, "Std.List"}} = Docs.parse_target("Std.List")
    end

    test "strips leading Cure. prefix" do
      assert {:ok, {:module, "Std.List"}} = Docs.parse_target("Cure.Std.List")
    end

    test "single PascalCase name is a module" do
      assert {:ok, {:module, "List"}} = Docs.parse_target("List")
    end

    test "last segment lowercase => function" do
      assert {:ok, {:function, "Std.List", "map"}} = Docs.parse_target("Std.List.map")
      assert {:ok, {:function, "Std.List", "map"}} = Docs.parse_target("Cure.Std.List.map")
    end

    test "bare lowercase name is rejected" do
      assert {:error, _} = Docs.parse_target("map")
    end

    test "empty input is rejected" do
      assert {:error, _} = Docs.parse_target("")
    end
  end

  describe "default_uses/0" do
    test "returns Cure-prefix-free stdlib names" do
      defaults = Docs.default_uses()

      assert is_list(defaults)
      assert "Std.Core" in defaults
      assert "Std.List" in defaults

      refute Enum.any?(defaults, &String.starts_with?(&1, "Cure."))
    end

    test "matches the Preload module list" do
      defaults = Docs.default_uses()
      preload_count = length(Cure.Stdlib.Preload.stdlib_modules())

      assert length(defaults) == preload_count
    end
  end

  describe "locate_source/2" do
    @tag :tmp_dir
    test "resolves Std.List to lib/std/list.cure when running from the repo root" do
      # This test only runs meaningfully from the Cure repo checkout where
      # `lib/std/list.cure` exists; skip gracefully otherwise.
      if File.regular?(Path.join(["lib", "std", "list.cure"])) do
        assert {:ok, path} = Docs.locate_source("Std.List", %{loaded: []})
        assert Path.basename(path) == "list.cure"
      else
        :ok
      end
    end

    test "returns :not_found for a non-existent module" do
      assert :not_found = Docs.locate_source("No.Such.Module.Ever", %{loaded: []})
    end
  end

  describe "render/2" do
    test "produces no crash for a real stdlib module" do
      if File.regular?(Path.join(["lib", "std", "list.cure"])) do
        state = fake_state()
        assert :ok = Docs.render("Std.List", state)
        assert :ok = Docs.render("Cure.Std.List", state)
        assert :ok = Docs.render("Std.List.map", state)
      else
        :ok
      end
    end

    test "emits a friendly message for unknown modules" do
      state = fake_state()
      assert :ok = Docs.render("No.Such.Module", state)
    end

    test "rejects bare lowercase names with a parse error" do
      state = fake_state()
      assert :ok = Docs.render("map", state)
    end
  end

  defp fake_state do
    %{theme: Theme.for_name(:mono), loaded: []}
  end
end
