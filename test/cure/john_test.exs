defmodule Cure.JohnTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  alias Cure.John

  setup do
    tmp =
      Path.join(System.tmp_dir!(), "cure_john_#{:erlang.unique_integer([:positive])}")

    File.mkdir_p!(tmp)
    on_exit(fn -> File.rm_rf!(tmp) end)
    {:ok, root: tmp}
  end

  describe "collect/1" do
    test "returns every top-level section", %{root: root} do
      snap = John.collect(root: root)

      # The five structural keys are always present, even when the project
      # is absent (then `:project` is `nil`) or the runtime is not started
      # (`:runtime` may still be present as a map with zero counts).
      assert %{
               at: %DateTime{},
               cure: %{},
               vm: %{},
               system: %{},
               tooling: %{},
               doctor: %{},
               logs: _
             } = snap

      assert Map.has_key?(snap, :project)
      assert Map.has_key?(snap, :runtime)
    end

    test "cure section carries the version and app state", %{root: root} do
      snap = John.collect(root: root)
      cure = snap.cure

      assert cure.version == Cure.version()
      assert cure.escript_main == "Cure.CLI"
      assert is_boolean(cure.app_loaded?)
      assert is_boolean(cure.app_started?)
      assert is_integer(cure.stdlib_loaded_modules)
    end

    test "vm section exposes scheduler and memory numbers", %{root: root} do
      snap = John.collect(root: root)
      vm = snap.vm

      assert is_integer(vm.schedulers)
      assert is_integer(vm.schedulers_online)
      assert vm.schedulers_online > 0
      assert vm.schedulers_online <= vm.schedulers
      assert is_integer(vm.process_count)
      assert vm.process_count > 0
      assert is_integer(vm.memory_total)
      assert vm.memory_total > 0
      assert vm.process_limit >= vm.process_count
    end

    test "system section includes OS and CWD info", %{root: root} do
      snap = John.collect(root: root)
      sys = snap.system

      assert is_atom(sys.os_family)
      assert is_atom(sys.os_name)
      assert is_binary(sys.cwd)
      assert is_binary(sys.arch)
    end

    test "tooling section includes loaded dependencies", %{root: root} do
      snap = John.collect(root: root)
      t = snap.tooling

      assert t.cure == Cure.version()
      assert is_list(t.dependencies)
      # :cure must be loaded for the test suite to run at all.
      assert Enum.any?(t.dependencies, fn {app, _} -> app == :cure end)
    end

    test "project is nil when no Cure.toml is present", %{root: root} do
      assert John.collect(root: root).project == nil
    end

    test "project is populated when Cure.toml exists", %{root: root} do
      File.write!(Path.join(root, "Cure.toml"), """
      [project]
      name = "john-test"
      version = "0.1.0"

      [dependencies]
      """)

      snap = John.collect(root: root)
      assert %{name: "john-test", version: "0.1.0"} = snap.project
      assert is_list(snap.project.dependencies)
      assert snap.project.lockfile == "missing"
    end

    test "doctor section summarises severity counts", %{root: root} do
      snap = John.collect(root: root)
      d = snap.doctor

      assert is_integer(d.info)
      assert is_integer(d.warnings)
      assert is_integer(d.errors)
      assert is_integer(d.total)
      assert d.total == d.info + d.warnings + d.errors
    end

    test "logs section returns a (possibly empty) list of entries", %{root: root} do
      log_dir = Path.join(root, ".cure/logs")
      File.mkdir_p!(log_dir)
      File.write!(Path.join(log_dir, "example.log"), "line 1\nline 2\nline 3\n")

      snap = John.collect(root: root)

      assert is_list(snap.logs)
      assert [entry] = snap.logs
      assert entry.path =~ "example.log"
      assert entry.size > 0
      assert entry.tail =~ "line 3"
    end
  end

  describe "render/2" do
    test "produces markdown with every required section", %{root: root} do
      snap = John.collect(root: root)
      md = John.render(snap, banner: true)

      assert md =~ "# Cure "
      assert md =~ "John"
      assert md =~ "## Cure"
      assert md =~ "## BEAM / OTP"
      assert md =~ "## System"
      assert md =~ "## Tooling"
      assert md =~ "## Project"
      assert md =~ "## Runtime"
      assert md =~ "## Doctor"
      assert md =~ "## Recent logs"
    end

    test "banner: false suppresses the dedication block", %{root: root} do
      snap = John.collect(root: root)
      md = John.render(snap, banner: false)

      refute md =~ "John Carbajal"
      assert md =~ "## Cure"
    end
  end

  describe "run/1" do
    test "writes a rendered report to the provided device", %{root: root} do
      output =
        capture_io(fn ->
          # `ansi: false` short-circuits both Marcli and the pure-Elixir
          # renderer, so we get the raw Markdown and can assert on
          # stable section headers without having to strip ANSI.
          John.run(root: root, ansi: false, banner: false)
        end)

      assert output =~ "## Cure"
      assert output =~ "## BEAM / OTP"
      assert output =~ "## System"
      assert output =~ "## Project"
    end
  end
end
