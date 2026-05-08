defmodule Cure.Project.CompileProjectTest do
  use ExUnit.Case, async: false

  defp setup_project(tmp, files) do
    File.mkdir_p!(Path.join(tmp, "lib"))

    Enum.each(files, fn {rel_path, contents} ->
      target = Path.join(tmp, rel_path)
      File.mkdir_p!(Path.dirname(target))
      File.write!(target, contents)
    end)
  end

  defp purge(modules) do
    Enum.each(modules, fn m ->
      :code.purge(m)
      :code.delete(m)
      :code.purge(m)
    end)
  end

  describe "[application] / [release] TOML parsing" do
    @tag :tmp_dir
    test "parses arrays of strings, booleans, ints, and nested env maps", %{tmp_dir: tmp} do
      File.write!(Path.join(tmp, "Cure.toml"), """
      [project]
      name = "demo"
      version = "0.4.2"

      [application]
      name           = "demo"
      vsn            = "0.4.2"
      applications   = ["logger", "crypto"]
      start_phases   = ["init", "warm_cache"]

      [application.env]
      port = 4000
      enabled = true

      [release]
      name         = "demo"
      vsn          = "0.4.2"
      include_erts = false
      applications = ["logger"]
      """)

      {:ok, project} = Cure.Project.load(tmp)
      assert project.application.name == "demo"
      assert project.application.applications == ["logger", "crypto"]
      assert project.application.start_phases == ["init", "warm_cache"]
      assert project.application.env["port"] == 4000
      assert project.application.env["enabled"] == true

      assert project.release.name == "demo"
      assert project.release.include_erts == false
      assert project.release.applications == ["logger"]
    end
  end

  describe "Cure.Project.detect_app/2" do
    @tag :tmp_dir
    test "returns nil when no app container exists", %{tmp_dir: tmp} do
      setup_project(tmp, [
        {"Cure.toml", "[project]\nname = \"demo\"\nversion = \"0.1.0\"\n"},
        {"lib/lib.cure", "mod Demo\n  fn hello() -> Atom = :ok\n"}
      ])

      {:ok, project} = Cure.Project.load(tmp)
      files = Path.wildcard(Path.join(tmp, "lib/**/*.cure"))
      assert {:ok, nil} = Cure.Project.detect_app(files, project)
    end

    @tag :tmp_dir
    test "returns the single app container when there is exactly one", %{tmp_dir: tmp} do
      setup_project(tmp, [
        {"Cure.toml", "[project]\nname = \"demo\"\nversion = \"0.1.0\"\n"},
        {"lib/app.cure", "app Demo\n"}
      ])

      {:ok, project} = Cure.Project.load(tmp)
      files = Path.wildcard(Path.join(tmp, "lib/**/*.cure"))
      assert {:ok, %{name: "Demo"}} = Cure.Project.detect_app(files, project)
    end

    @tag :tmp_dir
    test "returns {:error, :duplicate_app, _} when there are two", %{tmp_dir: tmp} do
      setup_project(tmp, [
        {"Cure.toml", "[project]\nname = \"demo\"\nversion = \"0.1.0\"\n"},
        {"lib/foo.cure", "app Foo\n"},
        {"lib/bar.cure", "app Bar\n"}
      ])

      {:ok, project} = Cure.Project.load(tmp)
      files = Path.wildcard(Path.join(tmp, "lib/**/*.cure"))
      assert {:error, {:duplicate_app, occurrences}} = Cure.Project.detect_app(files, project)
      assert length(occurrences) == 2
    end
  end

  describe "[compiler] stdlib_path parsing" do
    @tag :tmp_dir
    test "parses stdlib_path as a string value", %{tmp_dir: tmp} do
      File.write!(Path.join(tmp, "Cure.toml"), """
      [project]
      name = "demo"
      version = "0.1.0"

      [compiler]
      type_check = false
      stdlib_path = "/opt/cure/ebin"
      """)

      {:ok, project} = Cure.Project.load(tmp)
      assert Cure.Project.stdlib_path(project) == "/opt/cure/ebin"
    end

    @tag :tmp_dir
    test "stdlib_path returns nil when not set and CURE_LIB is unset", %{tmp_dir: tmp} do
      previous = System.get_env("CURE_LIB")

      try do
        System.delete_env("CURE_LIB")

        File.write!(Path.join(tmp, "Cure.toml"), """
        [project]
        name = "demo"
        version = "0.1.0"

        [compiler]
        type_check = false
        """)

        {:ok, project} = Cure.Project.load(tmp)
        assert Cure.Project.stdlib_path(project) == nil
      after
        case previous do
          nil -> System.delete_env("CURE_LIB")
          val -> System.put_env("CURE_LIB", val)
        end
      end
    end

    @tag :tmp_dir
    test "stdlib_path falls back to CURE_LIB when not set in toml", %{tmp_dir: tmp} do
      previous = System.get_env("CURE_LIB")

      try do
        System.put_env("CURE_LIB", "/fallback/ebin")

        File.write!(Path.join(tmp, "Cure.toml"), """
        [project]
        name = "demo"
        version = "0.1.0"

        [compiler]
        type_check = false
        """)

        {:ok, project} = Cure.Project.load(tmp)
        assert Cure.Project.stdlib_path(project) == "/fallback/ebin"
      after
        case previous do
          nil -> System.delete_env("CURE_LIB")
          val -> System.put_env("CURE_LIB", val)
        end
      end
    end
  end

  describe "missing stdlib module error" do
    test "use Std.Nonexistent produces :missing_stdlib_module error" do
      source = """
      mod Broken
        use Std.Nonexistent

        fn hello() -> Atom = :ok
      """

      assert {:error, {:codegen_error, {:missing_stdlib_module, :"Cure.Std.Nonexistent", _msg}}} =
               Cure.Compiler.compile_and_load(source, emit_events: false, check_types: false)
    end
  end

  describe "Cure.Project.compile_project/2" do
    @tag :tmp_dir
    test "compiles + emits .app resource for a minimal app project", %{tmp_dir: tmp} do
      setup_project(tmp, [
        {"Cure.toml",
         """
         [project]
         name = "minimal_app"
         version = "0.1.0"

         [application]
         name = "minimal_app"
         vsn  = "0.1.0"
         """},
        {"lib/app.cure", "app MinimalApp\n"}
      ])

      {:ok, project} = Cure.Project.load(tmp)
      ebin = Path.join(tmp, "_build/cure/ebin")

      try do
        assert {:ok, result} =
                 Cure.Project.compile_project(project, output_dir: ebin, emit_events: false)

        assert result.app_module == :"Cure.App.MinimalApp"
        assert File.exists?(Path.join(ebin, "minimal_app.app"))
        assert File.exists?(Path.join(ebin, "Cure.App.MinimalApp.beam"))
      after
        purge([:"Cure.App.MinimalApp"])
      end
    end

    @tag :tmp_dir
    test "rejects two app containers under E051", %{tmp_dir: tmp} do
      setup_project(tmp, [
        {"Cure.toml", "[project]\nname = \"demo\"\nversion = \"0.1.0\"\n"},
        {"lib/foo.cure", "app Foo\n"},
        {"lib/bar.cure", "app Bar\n"}
      ])

      {:ok, project} = Cure.Project.load(tmp)
      ebin = Path.join(tmp, "_build/cure/ebin")

      assert {:error, {:duplicate_app, _occurrences}} =
               Cure.Project.compile_project(project, output_dir: ebin, emit_events: false)
    end

    @tag :tmp_dir
    test "rejects a name mismatch with [application].name", %{tmp_dir: tmp} do
      setup_project(tmp, [
        {"Cure.toml",
         """
         [project]
         name = "demo"
         version = "0.1.0"

         [application]
         name = "other"
         """},
        {"lib/app.cure", "app Demo\n"}
      ])

      {:ok, project} = Cure.Project.load(tmp)
      ebin = Path.join(tmp, "_build/cure/ebin")

      assert {:error, {:app_name_mismatch, "other", "demo"}} =
               Cure.Project.compile_project(project, output_dir: ebin, emit_events: false)
    end
  end
end
