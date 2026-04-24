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
      assert entry.kind == :log
      assert entry.content =~ "line 3"
    end

    test "erl_crash.dump is summarised rather than tailed", %{root: root} do
      File.write!(Path.join(root, "erl_crash.dump"), """
      =erl_crash_dump:0.5
      Mon Apr 14 10:00:00 2026
      Slogan: eheap_alloc: Cannot allocate 1234567 bytes of memory (of type "heap").
      System version: Erlang/OTP 27 [erts-15.0] [source] [64-bit] [smp:16:16] [jit]
      Compiled: Fri Mar 21 18:13:23 2025
      Taints: crypto,zlib
      Atoms: 14723
      Calling Thread: scheduler:1
      =memory
      total: 55738344
      processes: 8388608
      processes_used: 8388608
      system: 47349736
      atom: 629657
      atom_used: 617923
      binary: 65856
      code: 17436712
      ets: 1165104
      =proc:<0.1.0>
      blah
      =proc:<0.2.0>
      blah
      =ets:<0.7.0>
      =mod:elixir
      =mod:erlang
      =mod:kernel
      """)

      snap = John.collect(root: root)
      assert [entry] = snap.logs
      assert entry.path =~ "erl_crash.dump"
      assert entry.kind == :crash_dump
      assert %{fields: fields, counts: counts} = entry.content

      as_map = Map.new(fields)
      assert as_map["format"] == "=erl_crash_dump:0.5"
      assert as_map["slogan"] =~ "Cannot allocate 1234567 bytes"
      assert as_map["system"] =~ "Erlang/OTP 27"
      assert as_map["atoms"] == "14723"
      assert as_map["taints"] == "crypto,zlib"
      assert as_map["memory total"] =~ ~r/\d/
      assert as_map["memory processes"] =~ ~r/\d/
      assert as_map["memory atom"] =~ ~r/\d/

      counts_map = Map.new(counts)
      assert counts_map["processes"] == 2
      assert counts_map["ets tables"] == 1
      assert counts_map["modules"] == 3
    end

    test "render/2 emits the crash-dump summary as Markdown bullets", %{root: root} do
      File.write!(Path.join(root, "erl_crash.dump"), """
      =erl_crash_dump:0.5
      Slogan: test slogan
      System version: test
      Atoms: 42
      =memory
      total: 1024
      """)

      snap = John.collect(root: root)
      md = John.render(snap, banner: false)

      assert md =~ "## Recent logs"
      assert md =~ "erl_crash.dump"
      assert md =~ "**slogan**"
      assert md =~ "test slogan"
      # The raw file content must NOT appear inside a code fence --
      # we now render the structured summary as bullets instead.
      refute md =~ "```\n=erl_crash_dump"
    end

    test "ill-formed UTF-8 in logs does not crash the renderer", %{root: root} do
      log_dir = Path.join(root, ".cure/logs")
      File.mkdir_p!(log_dir)
      # `0xC3 0x28` is an invalid UTF-8 sequence.
      File.write!(Path.join(log_dir, "ugly.log"), <<"prefix ", 0xC3, 0x28, " suffix\n">>)

      snap = John.collect(root: root)
      assert [entry] = snap.logs
      assert entry.kind == :log
      # The invalid byte was replaced rather than propagated as-is.
      assert String.valid?(entry.content)
      assert entry.content =~ "prefix"
      assert entry.content =~ "suffix"
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

    test "banner headline carries John's tagline and em dashes", %{root: root} do
      snap = John.collect(root: root)
      md = John.render(snap, banner: true)

      # Em dashes are literal U+2014 in the source so that both the
      # Marcli (MDEx) path and the pure-Elixir fallback renderer keep
      # them as text. See the comment above `banner_md/1`.
      assert md =~ "\u2014  John  \u2014"
      assert md =~ "What I need is visibility"
      # The long italic tribute paragraph was removed because `john`
      # is invoked many times per session.
      refute md =~ "*Named for"
    end

    test "banner: false suppresses the headline", %{root: root} do
      snap = John.collect(root: root)
      md = John.render(snap, banner: false)

      refute md =~ "What I need is visibility"
      # The headline line is `# Cure X.Y.Z  \u2014  John  \u2014  ...`.
      # Guard against `## Cure` (the section heading) being a
      # substring of any looser pattern.
      refute md =~ ~r/^# Cure /m
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
