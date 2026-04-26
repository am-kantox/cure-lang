defmodule Cure.CLI do
  @moduledoc """
  Standalone command-line interface for the Cure programming language.

  ## Subcommands

      cure compile <file|dir>   Compile .cure files to BEAM bytecode
      cure run <file>           Compile and execute a .cure file
      cure check <file>         Type-check a .cure file without compiling
      cure lsp                  Start the Language Server Protocol server
      cure stdlib               Compile the standard library
      cure version              Show the Cure version
      cure help                 Show this help message

  ## Options

      --output-dir DIR    Output directory for .beam files (default: _build/cure/ebin)
      --no-type-check     Skip type checking
      --optimize          Enable optimization passes
      --verbose           Show detailed compilation output
  """

  # Delegate to `Cure.version/0`, which is itself resolved at compile
  # time from the top-level `mix.exs` and marked as an
  # `@external_resource` so a version bump in `mix.exs` always reaches
  # the compiled escript.
  defp version, do: Cure.version()

  @doc "Entry point for escript."
  def main(args) do
    # Ensure the application is started
    Application.ensure_all_started(:cure)

    {opts, rest, _} =
      OptionParser.parse(args,
        switches: [
          output_dir: :string,
          type_check: :boolean,
          optimize: :boolean,
          verbose: :boolean,
          help: :boolean,
          goal: :string,
          ctx: :string,
          effects: :string,
          max: :integer,
          depth: :integer,
          duration: :integer,
          width: :integer,
          action: :string,
          template: :string,
          lib: :boolean,
          app: :boolean,
          fsm: :boolean,
          filter: :string,
          doctests: :boolean,
          poll_ms: :integer,
          debounce: :integer,
          aggressive: :boolean,
          ast: :boolean,
          algebra: :boolean,
          safe: :boolean,
          check: :boolean,
          dry_run: :boolean,
          hex: :boolean,
          handle: :string,
          token: :string,
          cover: :boolean,
          strict: :boolean,
          registry: :string,
          include_erts: :boolean,
          overwrite: :boolean,
          title: :string,
          main: :string,
          extras: :keep,
          # v0.31.0 -- monomorphisation + PGO
          monomorphise: :boolean,
          pgo: :boolean,
          record_profile: :boolean,
          profile_dir: :string,
          module: :string,
          top: :integer
        ],
        aliases: [o: :output_dir, v: :verbose, h: :help, f: :filter, t: :template]
      )

    if opts[:help] do
      help()
    else
      case rest do
        ["compile" | paths] ->
          cmd_compile(paths, opts)

        ["run" | [path]] ->
          cmd_run(path, opts)

        ["check" | [path]] ->
          cmd_check(path, opts)

        ["lsp"] ->
          cmd_lsp()

        ["stdlib"] ->
          cmd_stdlib(opts)

        ["version"] ->
          cmd_version()

        ["init" | [name]] ->
          cmd_init(name)

        ["deps"] ->
          cmd_deps()

        ["deps", "update"] ->
          cmd_deps_update()

        ["deps", "tree"] ->
          cmd_deps_tree()

        ["test"] ->
          cmd_test(opts)

        ["explain"] ->
          cmd_explain_all()

        ["explain" | [code]] ->
          cmd_explain(code)

        ["doc" | paths] ->
          cmd_doc(paths, opts)

        ["repl"] ->
          cmd_repl()

        ["fmt" | paths] ->
          cmd_fmt(paths, opts)

        ["watch" | rest] ->
          cmd_watch(rest, opts)

        ["new" | rest] ->
          cmd_new(rest, opts)

        ["bench" | rest] ->
          cmd_bench(rest, opts)

        ["why"] ->
          cmd_explain_all()

        ["why" | [code]] ->
          cmd_explain(code)

        ["doctor"] ->
          cmd_doctor(opts)

        ["fix"] ->
          cmd_fix(opts)

        ["publish" | _] ->
          cmd_publish(opts)

        ["search" | [query]] ->
          cmd_search(query, opts)

        ["info" | [name]] ->
          cmd_info(name, opts)

        ["keys", "generate", handle] ->
          cmd_keys_generate(handle)

        ["keys", "list"] ->
          cmd_keys_list()

        ["release" | rest] ->
          cmd_release(rest, opts)

        ["top"] ->
          cmd_top(opts)

        ["john"] ->
          cmd_john(opts)

        ["trace" | rest] ->
          cmd_trace(rest, opts)

        ["synth" | rest] ->
          cmd_synth(rest, opts)

        ["bless" | rest] ->
          cmd_bless(rest)

        ["replay" | rest] ->
          cmd_replay(rest, opts)

        ["profile"] ->
          cmd_profile(["show"], opts)

        ["profile" | rest] ->
          cmd_profile(rest, opts)

        ["draw" | rest] ->
          cmd_draw(rest, opts)

        ["verify" | rest] ->
          cmd_verify(rest, opts)

        ["export-types" | rest] ->
          cmd_export_types(rest, opts)

        ["snap" | rest] ->
          cmd_snap(rest, opts)

        ["story" | _] ->
          cmd_story(opts)

        ["help"] ->
          help()

        [] ->
          help()

        [unknown | _] ->
          known_commands = ~w(
            compile run check lsp stdlib version init deps test
            explain doc repl fmt watch new bench why doctor fix
            publish search info keys release top trace synth bless replay
            john profile draw verify export-types snap story help
          )

          suffix =
            case Cure.Compiler.Errors.suggest(unknown, known_commands) do
              nil -> ""
              suggestion -> " Did you mean '#{suggestion}'?"
            end

          error("Unknown command: #{unknown}.#{suffix} Run 'cure help' for usage.")
      end
    end
  end

  # -- replay (v0.28.0) --------------------------------------------------------

  defp cmd_replay([], _opts) do
    error("Usage: cure replay <path.journal> [--module ModuleName] [--step]")
    exit({:shutdown, 1})
  end

  defp cmd_replay([path | _], opts) do
    step? = Keyword.get(opts, :step, false)
    mod_str = Keyword.get(opts, :module)

    case Cure.Observe.Journal.load(path) do
      {:error, reason} ->
        error("Cannot load #{path}: #{inspect(reason)}")
        exit({:shutdown, 1})

      {:ok, entries} ->
        info("Loaded #{length(entries)} entries from #{path}")
        Cure.Observe.Replay.print_trace(entries)

        if mod_str do
          mod = Module.concat([mod_str])

          if Code.ensure_loaded?(mod) do
            case Cure.Observe.Replay.replay(mod, entries, step: step?) do
              {:ok, :quit} ->
                info("Replay quit early.")

              {:ok, _results} ->
                info("Replay complete.")

              {:error, reason} ->
                error("Replay failed: #{inspect(reason)}")
                exit({:shutdown, 1})
            end
          else
            error("Module #{mod_str} not loaded. Run 'cure compile' first.")
            exit({:shutdown, 1})
          end
        end
    end
  end

  # -- bless (v0.28.0) ---------------------------------------------------------

  defp cmd_bless([]) do
    error("Usage: cure bless path/to/file.cure")
    exit({:shutdown, 1})
  end

  defp cmd_bless(paths) do
    Enum.each(paths, fn path ->
      info("Blessing #{path}...")

      case Cure.Bless.bless_file(path) do
        :nothing_to_fix ->
          info("  No type errors found.")

        :all_fixed ->
          info("  All errors fixed.")

        :some_skipped ->
          info("  Some errors remain (skipped or declined).")

        {:error, reason} ->
          error("  #{reason}")
          exit({:shutdown, 1})
      end
    end)
  end

  # -- top / trace / synth (v0.27.0) -------------------------------------------

  defp cmd_top(opts) do
    width = Keyword.get(opts, :width, 80)
    snapshot = Cure.Observe.Top.snapshot()
    IO.puts(Cure.Observe.Top.render(snapshot, width: width))
  end

  # -- john (everything, all at once) ------------------------------------------

  defp cmd_john(opts) do
    john_opts =
      []
      |> put_if(opts, :width)

    _ = Cure.John.run(john_opts)
  end

  defp put_if(keyword, opts, key) do
    case Keyword.fetch(opts, key) do
      {:ok, value} -> Keyword.put(keyword, key, value)
      :error -> keyword
    end
  end

  defp cmd_trace([], _opts), do: error("Usage: cure trace Module.fun/arity")

  defp cmd_trace([target | _], opts) do
    duration = Keyword.get(opts, :duration, 10) * 1000

    case parse_mfa(target) do
      {:ok, mfa} ->
        info("Tracing #{target} for #{div(duration, 1000)}s...")
        Cure.Observe.Trace.start(mfa)
        :timer.sleep(duration)
        Cure.Observe.Trace.stop()
        info("Trace stopped.")

      {:error, _} ->
        error("Cannot parse #{inspect(target)}; expected Module.fun/arity")
        exit({:shutdown, 1})
    end
  end

  defp cmd_synth(_rest, opts) do
    case Keyword.get(opts, :goal) do
      nil ->
        error("Usage: cure synth --goal T [--ctx name=T[,...]] [--effects io,state]")
        exit({:shutdown, 1})

      goal ->
        do_synth(goal, opts)
    end
  end

  defp do_synth(goal, opts) do
    ctx = parse_synth_ctx(Keyword.get(opts, :ctx, ""))
    effects = parse_synth_effects(Keyword.get(opts, :effects, ""))
    max_results = Keyword.get(opts, :max, 3)
    depth = Keyword.get(opts, :depth, 3)

    info("goal: #{goal}")
    info("ctx:  #{inspect(ctx, pretty: true)}")

    candidates =
      Cure.Types.Synth.synthesise(goal, ctx, %{},
        effects: effects,
        max: max_results,
        depth: depth
      )

    case candidates do
      [] ->
        info("No candidates found within the budget (E061).")

      _ ->
        info("\nCandidates:")

        candidates
        |> Enum.with_index(1)
        |> Enum.each(fn {c, i} ->
          tag =
            if c.effects == [], do: "pure", else: "! " <> Enum.map_join(c.effects, ",", &to_string/1)

          info("  #{i}. #{c.expr}  (cost #{c.cost}, #{tag})")
        end)
    end
  end

  defp parse_mfa(target) when is_binary(target) do
    case Regex.run(~r/^([\w\.]+)\.(\w+)\/(\d+)$/, target) do
      [_, mod, fun, arity] ->
        mod_atom = Module.concat([mod])
        {:ok, {mod_atom, String.to_atom(fun), String.to_integer(arity)}}

      _ ->
        {:error, :bad_mfa}
    end
  end

  defp parse_synth_ctx(""), do: %{}

  defp parse_synth_ctx(str) do
    str
    |> String.split(",", trim: true)
    |> Enum.flat_map(fn binding ->
      case String.split(binding, "=", parts: 2) do
        [name, type] -> [{String.trim(name), String.trim(type)}]
        _ -> []
      end
    end)
    |> Map.new()
  end

  defp parse_synth_effects(""), do: []

  defp parse_synth_effects(str) do
    str
    |> String.split(",", trim: true)
    |> Enum.map(&String.trim/1)
    |> Enum.map(&String.to_atom/1)
  end

  # -- compile -----------------------------------------------------------------

  defp cmd_compile([], _opts), do: error("Usage: cure compile <file|directory>")

  defp cmd_compile(paths, opts) do
    output_dir = Keyword.get(opts, :output_dir, "_build/cure/ebin")
    check? = Keyword.get(opts, :type_check, true)
    optimize? = Keyword.get(opts, :optimize, false)
    verbose? = Keyword.get(opts, :verbose, false)
    monomorphise? = Keyword.get(opts, :monomorphise, true)
    pgo? = Keyword.get(opts, :pgo, false)
    profile_dir = Keyword.get(opts, :profile_dir, Cure.PGO.Recorder.default_dir())

    # Preload the stdlib so sources that `use Std.Iter`, `use Std.Gen`,
    # etc. can resolve their imports at compile time. Without this, a
    # fresh VM hitting a bulk `cure compile examples/` run would see
    # `undefined_function` lint errors for any module referencing a
    # stdlib function whose beam has not yet been loaded.
    preload_stdlib()

    base_compile_opts = [
      output_dir: output_dir,
      check_types: check?,
      optimize: optimize?,
      monomorphise: monomorphise?,
      emit_events: false
    ]

    compile_opts =
      if pgo? do
        case Cure.PGO.load(profile_dir, emit_events: false) do
          {:ok, pgo} ->
            if verbose?,
              do: info("PGO loaded from #{profile_dir}: #{MapSet.size(pgo.hot)} hot, #{MapSet.size(pgo.cold)} cold")

            Keyword.put(base_compile_opts, :pgo, pgo)

          {:error, reason} ->
            warn("--pgo: cannot load #{profile_dir}: #{inspect(reason)}; continuing without PGO")
            base_compile_opts
        end
      else
        base_compile_opts
      end

    Enum.each(paths, fn path ->
      if File.dir?(path) do
        path
        |> Path.join("**/*.cure")
        |> Path.wildcard()
        |> Enum.each(&compile_one(&1, compile_opts, verbose?))
      else
        compile_one(path, compile_opts, verbose?)
      end
    end)
  end

  defp compile_one(path, opts, verbose?) do
    if verbose?, do: info("Compiling #{path}")

    case Cure.Compiler.compile_file(path, opts) do
      {:ok, module, warnings} ->
        Enum.each(warnings, fn w -> warn("  #{inspect(w)}") end)
        info("  -> #{module}")

      {:error, reason} ->
        source = File.read(path) |> elem(1)
        formatted = Cure.Compiler.Errors.format_with_source(reason, path, source || "")
        # `formatted` already carries the `error: <category>` diagnostic;
        # go straight to stderr so `error/1`'s own `error: ` prefix does
        # not double-wrap the output.
        diagnostic(formatted)
        exit({:shutdown, 1})
    end
  end

  # -- run ---------------------------------------------------------------------

  @dialyzer {:nowarn_function, cmd_run: 2}
  defp cmd_run(path, opts) do
    # Type checking runs by default; use `--no-type-check` to opt out.
    check? = Keyword.get(opts, :type_check, true)
    optimize? = Keyword.get(opts, :optimize, false)
    monomorphise? = Keyword.get(opts, :monomorphise, true)
    record_profile? = Keyword.get(opts, :record_profile, false)
    profile_dir = Keyword.get(opts, :profile_dir, Cure.PGO.Recorder.default_dir())

    preload_stdlib()

    if record_profile? do
      case Cure.PGO.Recorder.start_link([]) do
        {:ok, _} -> :ok
        {:error, {:already_started, _}} -> :ok
        other -> warn("--record-profile: failed to start recorder: #{inspect(other)}")
      end
    end

    source =
      case File.read(path) do
        {:ok, s} -> s
        {:error, reason} -> error("Cannot read #{path}: #{reason}") && exit({:shutdown, 1})
      end

    case Cure.Compiler.compile_and_load(source,
           file: path,
           check_types: check?,
           optimize: optimize?,
           monomorphise: monomorphise?,
           emit_events: false
         ) do
      {:ok, module} ->
        if function_exported?(module, :main, 0) do
          result = module.main()
          if result != :ok and result != nil, do: IO.inspect(result)
        else
          info("Module #{module} compiled (no main/0 function)")
        end

        if record_profile? do
          case Cure.PGO.Recorder.flush(profile_dir) do
            {:ok, []} -> info("--record-profile: no profile entries collected")
            {:ok, paths} -> info("--record-profile: wrote #{length(paths)} profile(s) to #{profile_dir}")
            {:error, reason} -> warn("--record-profile: flush failed: #{inspect(reason)}")
          end
        end

      {:error, reason} ->
        formatted = Cure.Compiler.Errors.format_error(reason, path)
        diagnostic(formatted)
        exit({:shutdown, 1})
    end
  end

  # -- profile (v0.31.0) -------------------------------------------------------

  defp cmd_profile(["show" | _rest], opts) do
    dir = Keyword.get(opts, :profile_dir, Cure.PGO.Recorder.default_dir())
    top_n = Keyword.get(opts, :top, 10)

    case Cure.PGO.load(dir, emit_events: false) do
      {:error, reason} ->
        error("cannot load profiles from #{dir}: #{inspect(reason)}")
        exit({:shutdown, 1})

      {:ok, pgo} ->
        info("PGO summary (#{dir})")
        info("  hot:  #{MapSet.size(pgo.hot)} function(s)")
        info("  cold: #{MapSet.size(pgo.cold)} function(s)")
        info("  threshold: #{pgo.hot_threshold}")

        if MapSet.size(pgo.hot) > 0 do
          info("\nHot (top #{top_n}):")

          pgo.hot
          |> Enum.take(top_n)
          |> Enum.each(fn {m, f, a} -> info("  #{m}.#{f}/#{a}") end)
        end
    end
  end

  defp cmd_profile(["clear" | _rest], opts) do
    dir = Keyword.get(opts, :profile_dir, Cure.PGO.Recorder.default_dir())

    case File.ls(dir) do
      {:error, _} ->
        info("profile dir #{dir} is empty or missing")

      {:ok, files} ->
        removed =
          files
          |> Enum.filter(&String.ends_with?(&1, ".profile"))
          |> Enum.map(fn f ->
            path = Path.join(dir, f)
            File.rm!(path)
            path
          end)

        info("removed #{length(removed)} profile(s) from #{dir}")
    end
  end

  defp cmd_profile(["run" | rest], opts) do
    case rest do
      [path | _] ->
        cmd_run(path, Keyword.put(opts, :record_profile, true))

      [] ->
        error("Usage: cure profile run <file.cure>")
        exit({:shutdown, 1})
    end
  end

  defp cmd_profile([unknown | _], _opts) do
    error("Unknown profile subcommand: #{unknown}. Use one of: run, show, clear")
    exit({:shutdown, 1})
  end

  # -- draw (v0.31.0) ----------------------------------------------------------

  defp cmd_draw([], _opts) do
    error("Usage: cure draw <path.cure> [--filter fsm|sup|app]")
    exit({:shutdown, 1})
  end

  defp cmd_draw([kind, path], opts) when kind in ["fsm", "sup", "app"] do
    do_draw(path, Keyword.put(opts, :filter, String.to_atom(kind)))
  end

  defp cmd_draw([path | _rest], opts) do
    filter =
      case Keyword.get(opts, :filter) do
        nil -> :all
        "fsm" -> :fsm
        "sup" -> :sup
        "app" -> :app
        "all" -> :all
        atom when is_atom(atom) -> atom
        _ -> :all
      end

    do_draw(path, Keyword.put(opts, :filter, filter))
  end

  defp do_draw(path, opts) do
    filter = Keyword.get(opts, :filter, :all)

    case Cure.Doc.Ascii.render_file(path, filter: filter) do
      {:ok, ""} ->
        info("#{path}: no fsm/sup/app containers to draw")

      {:ok, source} ->
        IO.puts(source)

      {:error, reason} ->
        error("cannot draw #{path}: #{inspect(reason)}")
        exit({:shutdown, 1})
    end
  end

  # Load stdlib .beam files from _build/cure/ebin (plus any Cure.* example
  # modules previously compiled into _build/cure/ex_ebin) into the VM.
  #
  # The dedicated helper avoids adding the output directories to the
  # global Erlang code path, so stale leftover lowercase beams (e.g. a
  # pre-rename examples/math.cure -> math.beam) can't shadow OTP modules.
  defp preload_stdlib do
    # CLI entry points (`cure run`, `cure compile`) want every stdlib
    # module available so user sources can `use Std.X` without thinking
    # about groups. The REPL is the only caller with a narrower default
    # (`:none`); see `Cure.REPL.start/1`.
    Cure.Stdlib.Preload.preload(examples: true, kind: :all)
  end

  # -- check -------------------------------------------------------------------

  @dialyzer {:nowarn_function, cmd_check: 2}
  defp cmd_check(path, _opts) do
    source =
      case File.read(path) do
        {:ok, s} -> s
        {:error, reason} -> error("Cannot read #{path}: #{reason}") && exit({:shutdown, 1})
      end

    with {:ok, tokens} <- Cure.Compiler.Lexer.tokenize(source, file: path, emit_events: false),
         {:ok, ast} <- Cure.Compiler.Parser.parse(tokens, file: path, emit_events: false),
         {:ok, _} <- Cure.Types.Checker.check_module(ast, file: path, emit_events: false) do
      info("#{path}: OK")
    else
      {:error, reason} ->
        # `Checker.check_module/2` returns a bare list of diagnostics;
        # every other pipeline stage returns a tagged tuple. Funnel both
        # through `format_error/2` (which now accepts raw lists) and
        # print the already-formatted string directly to stderr.
        formatted = Cure.Compiler.Errors.format_error(reason, path)
        diagnostic(formatted)
        exit({:shutdown, 1})
    end
  end

  # -- lsp ---------------------------------------------------------------------

  defp cmd_lsp do
    {:ok, _pid} = Cure.LSP.Server.start_link()
    Process.sleep(:infinity)
  end

  # -- stdlib ------------------------------------------------------------------

  defp cmd_stdlib(opts) do
    output_dir = Keyword.get(opts, :output_dir, "_build/cure/ebin")
    stdlib_dir = Path.join([:code.priv_dir(:cure) |> to_string(), "..", "lib", "std"])

    stdlib_dir =
      if File.dir?(stdlib_dir) do
        stdlib_dir
      else
        Path.join(["lib", "std"])
      end

    cure_files = Path.wildcard(Path.join(stdlib_dir, "*.cure")) |> Enum.sort()

    if cure_files == [] do
      info("No .cure files found in #{stdlib_dir}")
    else
      info("Compiling Cure standard library (#{length(cure_files)} modules)")

      Enum.each(cure_files, fn path ->
        name = Path.basename(path, ".cure")

        case Cure.Compiler.compile_file(path, output_dir: output_dir, emit_events: false) do
          {:ok, module, _} -> info("  #{name} -> #{module}")
          {:error, reason} -> error("  #{name}: #{inspect(reason)}")
        end
      end)

      info("Output: #{output_dir}")
    end
  end

  # -- init --------------------------------------------------------------------

  defp cmd_init(name) do
    Cure.Project.init(name)
    info("Created project '#{name}' with Cure.toml, lib/main.cure")
  end

  # -- deps --------------------------------------------------------------------

  defp cmd_deps do
    case Cure.Project.load() do
      {:ok, project} ->
        # `cure deps` may have to compile path/git dependencies that
        # `use Std.*`. Preload the full stdlib up front so those
        # imports resolve at compile time without extra plumbing.
        preload_stdlib()

        case project.dependencies do
          [] ->
            Cure.Project.write_lock(project)
            info("No dependencies declared in Cure.toml; lockfile is up to date.")

          deps ->
            info("Resolving #{length(deps)} dependency(ies) for #{project.name}...")

            case Cure.Project.resolve_deps(project) do
              :ok ->
                Cure.Project.write_lock(project)
                info("Dependencies resolved. Cure.lock written.")

              {:error, reason} ->
                error("Failed to resolve dependencies: #{inspect(reason)}")
                exit({:shutdown, 1})
            end
        end

      {:error, :no_project_file} ->
        error("No Cure.toml found in current directory. Run `cure new <name>` first.")
        exit({:shutdown, 1})

      {:error, reason} ->
        error("Cannot load Cure.toml: #{inspect(reason)}")
        exit({:shutdown, 1})
    end
  end

  defp cmd_deps_update do
    case Cure.Project.load() do
      {:ok, project} ->
        preload_stdlib()

        case project.dependencies do
          [] ->
            info("No dependencies to update.")

          deps ->
            info("Updating #{length(deps)} dependency(ies) for #{project.name}...")

            Enum.each(deps, fn dep ->
              # `resolve_git_dep/2` clones into `_build/deps/<name>` and
              # compiles the dep's `lib/`. Today it always returns
              # `:ok` (it raises on failure), so the bare assignment
              # below is sufficient; if it ever grows an `{:error, _}`
              # tag we will get a `MatchError` here and notice.
              if Map.get(dep, :git) do
                :ok = Cure.Project.resolve_git_dep(dep, project.root)
              end
            end)

            Cure.Project.write_lock(project)
            info("Lockfile updated.")
        end

      {:error, :no_project_file} ->
        error("No Cure.toml found in current directory.")
        exit({:shutdown, 1})

      {:error, reason} ->
        error("Cannot load Cure.toml: #{inspect(reason)}")
        exit({:shutdown, 1})
    end
  end

  defp cmd_deps_tree do
    case Cure.Project.load() do
      {:ok, project} ->
        IO.puts(Cure.Project.dep_tree(project))

      {:error, :no_project_file} ->
        error("No Cure.toml found in current directory.")
        exit({:shutdown, 1})

      {:error, reason} ->
        error("Cannot load Cure.toml: #{inspect(reason)}")
        exit({:shutdown, 1})
    end
  end

  # -- test --------------------------------------------------------------------

  defp cmd_test(opts) do
    filter = Keyword.get(opts, :filter, nil)
    doctests? = Keyword.get(opts, :doctests, false)
    cover? = Keyword.get(opts, :cover, false)

    if cover? do
      Cure.Cover.start("_build/cure/ebin")
    end

    # Tests typically reference both stdlib helpers (`Std.Test.assert_eq`)
    # and modules defined in the project's own `lib/`. The escript starts
    # with neither loaded, so without this step every test that calls
    # into `lib/` or `Std.*` would crash with `:undef`. Mirror what
    # `cmd_run/2` does for stdlib, then JIT-compile every `lib/**/*.cure`
    # so user modules (`Money.hello/0`, etc.) are reachable from the
    # test bodies below.
    preload_stdlib()
    load_project_lib()

    test_files = Path.wildcard("test/**/*.cure")

    if test_files == [] do
      info("No test files found in test/")
    else
      results =
        Enum.map(test_files, fn file ->
          case Cure.Compiler.compile_and_load(File.read!(file), file: file, emit_events: false) do
            {:ok, mod} ->
              # Run all test_ functions
              exports = mod.module_info(:exports)

              test_fns =
                exports
                |> Enum.filter(fn {name, arity} ->
                  String.starts_with?(Atom.to_string(name), "test") and arity == 0
                end)
                |> Enum.filter(fn {name, _} ->
                  filter == nil or String.contains?(Atom.to_string(name), filter)
                end)

              Enum.map(test_fns, fn {name, _} ->
                try do
                  apply(mod, name, [])
                  {:pass, "#{file}: #{name}"}
                catch
                  _, reason -> {:fail, "#{file}: #{name} -- #{inspect(reason)}"}
                end
              end)

            {:error, _} ->
              [{:fail, "#{file}: compilation error"}]
          end
        end)
        |> List.flatten()

      results =
        if doctests? do
          results ++ run_doctests(filter)
        else
          results
        end

      pass = Enum.count(results, fn {s, _} -> s == :pass end)
      fail = Enum.count(results, fn {s, _} -> s == :fail end)

      Enum.each(results, fn
        {:pass, name} -> info("  PASS #{name}")
        {:fail, name} -> error("  FAIL #{name}")
      end)

      info("#{pass} passed, #{fail} failed")

      if cover? do
        results_cov = Cure.Cover.collect()
        _ = Cure.Cover.summary(results_cov)
        _ = Cure.Cover.report(results_cov)
        info("Coverage HTML written to _build/cure/cover/index.html")
      end

      if fail > 0, do: exit({:shutdown, 1})
    end
  end

  # Compile and load every `lib/**/*.cure` in the current project so
  # test bodies can call into user modules without each test having to
  # bootstrap the project itself. Failures are surfaced as warnings
  # rather than aborting the whole `cure test` run -- a broken module
  # in `lib/` will already produce a follow-up `:undef` from the test
  # that depends on it, which is more actionable than a single
  # "compilation error" line.
  defp load_project_lib do
    "lib/**/*.cure"
    |> Path.wildcard()
    |> Enum.sort()
    |> Enum.each(fn file ->
      case Cure.Compiler.compile_and_load(File.read!(file), file: file, emit_events: false) do
        {:ok, _module} ->
          :ok

        {:error, reason} ->
          warn("#{file}: #{inspect(reason)}")
      end
    end)
  end

  defp run_doctests(filter) do
    Path.wildcard("lib/**/*.cure")
    |> Enum.flat_map(fn file ->
      case Cure.Doc.Doctests.extract(file) do
        [] ->
          []

        cases ->
          cases
          |> Enum.filter(fn %{name: n} -> filter == nil or String.contains?(n, filter) end)
          |> Enum.map(fn %{name: name, expr: expr, expected: expected} ->
            case Cure.Doc.Doctests.run_one(expr, expected) do
              :ok -> {:pass, "#{file}: doctest #{name}"}
              {:fail, reason} -> {:fail, "#{file}: doctest #{name} -- #{reason}"}
            end
          end)
      end
    end)
  end

  # -- doc ---------------------------------------------------------------------
  #
  # `cure doc` reads `Cure.toml`'s optional `[doc]` table, lets the
  # user override the most interesting fields (`--title`, `--main`,
  # `--extras`) from the command line, then hands everything to the
  # generator. When `Cure.toml` is absent we fall back to sensible
  # defaults (title = "Cure Documentation", no extras, no groups).
  defp cmd_doc(paths, opts) do
    output_dir = Keyword.get(opts, :output_dir, "_build/cure/doc")
    project_root = File.cwd!()
    {project_doc, project_title} = load_doc_config(project_root)

    cli_extras = Keyword.get_values(opts, :extras)

    doc_config =
      project_doc
      |> Map.put(
        :extras,
        if(cli_extras == [], do: Map.get(project_doc, :extras, []), else: cli_extras)
      )
      |> Map.put(:main, Keyword.get(opts, :main, Map.get(project_doc, :main)))

    title =
      Keyword.get(opts, :title) ||
        Map.get(project_doc, :title) ||
        project_title

    cure_files =
      case paths do
        [] ->
          Path.wildcard("lib/**/*.cure") ++ Path.wildcard("lib/std/*.cure")

        _ ->
          Enum.flat_map(paths, fn p ->
            if File.dir?(p), do: Path.wildcard(Path.join(p, "**/*.cure")), else: [p]
          end)
      end

    if cure_files == [] do
      info("No .cure files found")
    else
      info("Generating documentation for #{length(cure_files)} files")

      modules =
        Enum.flat_map(cure_files, fn file ->
          source = File.read!(file)

          with {:ok, tokens} <- Cure.Compiler.Lexer.tokenize(source, file: file, emit_events: false),
               {:ok, ast} <- Cure.Compiler.Parser.parse(tokens, file: file, emit_events: false) do
            doc = Cure.Doc.Extractor.extract(ast)

            if doc.module != "Unknown" do
              [doc]
            else
              []
            end
          else
            _ -> []
          end
        end)

      Cure.Doc.HTMLGenerator.generate(modules, output_dir,
        title: title,
        doc_config: doc_config,
        project_root: project_root,
        cure_version: Cure.version()
      )

      extras_count = length(Map.get(doc_config, :extras, []))

      info("Documentation written to #{output_dir}/ (#{length(modules)} modules, #{extras_count} extras)")
    end
  end

  # Load the `[doc]` table from `Cure.toml`, returning `{doc_map,
  # fallback_title}`. The fallback title is derived from `[project]`
  # so a bare `Cure.toml` still produces a branded docset.
  defp load_doc_config(root) do
    case Cure.Project.load(root) do
      {:ok, project} ->
        title =
          case project.name do
            n when is_binary(n) and n != "" ->
              String.capitalize(n) <> " Documentation"

            _ ->
              "Cure Documentation"
          end

        {project.doc, title}

      _ ->
        {%{}, "Cure Documentation"}
    end
  end

  # -- repl --------------------------------------------------------------------

  defp cmd_repl do
    Cure.REPL.start()
  end

  # -- fmt ---------------------------------------------------------------------

  # Four modes:
  #
  #   * (default, v0.21.0) algebra pretty-printer. Reformats from the
  #     AST using `Cure.Compiler.Algebra` + `Cure.Compiler.AlgebraFormatter`,
  #     with round-trip verification that falls back to the original
  #     source when the rewrite would change program structure. Plain
  #     `#` comment nodes and doc comments survive the round-trip.
  #
  #   * `--safe`: legacy byte-level formatter from v0.20.0, kept as an
  #     escape hatch for sources that have layout the algebra formatter
  #     does not yet support.
  #
  #   * `--algebra`: explicit opt-in; synonymous with the default.
  #
  #   * `--aggressive` / `--ast`: canonicalising AST pretty printer.
  #     Reformats the buffer from the parse tree through
  #     `Cure.Compiler.Printer`, which strips plain `#` comments and
  #     any layout that doesn't survive a parser round-trip. Prints a
  #     banner before touching disk so users know what they're opting
  #     into.
  #
  #   * `--check`: dry-run that prints which files would change without
  #     rewriting them. Uses the algebra formatter in v0.21.0.
  defp cmd_fmt(paths, opts) do
    cure_files =
      case paths do
        [] ->
          Path.wildcard("lib/**/*.cure") ++ Path.wildcard("test/**/*.cure")

        _ ->
          Enum.flat_map(paths, fn p ->
            if File.dir?(p), do: Path.wildcard(Path.join(p, "**/*.cure")), else: [p]
          end)
      end

    cond do
      cure_files == [] ->
        info("No .cure files found")

      Keyword.get(opts, :aggressive, false) or Keyword.get(opts, :ast, false) ->
        fmt_aggressive(cure_files)

      Keyword.get(opts, :safe, false) ->
        fmt_safe(cure_files)

      Keyword.get(opts, :check, false) ->
        fmt_check(cure_files)

      Keyword.get(opts, :dry_run, false) ->
        fmt_diff(cure_files)

      true ->
        # v0.21.0: algebra formatter is the default. The explicit
        # `--algebra` flag is kept for symmetry with `--safe` but
        # otherwise a no-op.
        fmt_algebra(cure_files)
    end
  end

  # v0.21.0: algebra formatter is now the default. It renders the
  # buffer from the AST using `Cure.Compiler.Algebra` and
  # `Cure.Compiler.AlgebraFormatter`, with round-trip verification that
  # falls back to the original source when the rewrite would change
  # program structure.
  defp fmt_algebra(files) do
    Enum.each(files, fn file ->
      source = File.read!(file)

      case Cure.Compiler.Formatter.format_algebra(source) do
        {:ok, ^source} ->
          :ok

        {:ok, formatted} ->
          File.write!(file, formatted)
          info("  formatted (algebra) #{file}")
      end
    end)
  end

  defp fmt_safe(files) do
    Enum.each(files, fn file ->
      source = File.read!(file)

      case Cure.Compiler.Formatter.format(source) do
        {:ok, ^source} ->
          :ok

        {:ok, formatted} ->
          File.write!(file, formatted)
          info("  formatted #{file}")
      end
    end)
  end

  # `cure fmt --diff` (--dry-run flag): shows a red/green unified diff
  # for every file that would be reformatted, without touching disk.
  # Exits with code 1 when any file has pending changes (CI-friendly).
  defp fmt_diff(files) do
    changed =
      Enum.reduce(files, 0, fn file, count ->
        source = File.read!(file)
        {:ok, formatted} = Cure.Compiler.Formatter.format_algebra(source)

        if formatted == source do
          count
        else
          render_unified_diff(file, source, formatted)
          count + 1
        end
      end)

    if changed == 0 do
      info("All files are formatted")
    else
      error("#{changed} file(s) would be reformatted")
      exit({:shutdown, 1})
    end
  end

  # Render a colour-annotated unified diff of two multi-line strings.
  # Red lines (-) are present in `original` but not in `formatted`.
  # Green lines (+) are present in `formatted` but not in `original`.
  # Uses `List.myers_difference/2` so the output is minimal and
  # stable. No external tooling required.
  defp render_unified_diff(file, original, formatted) do
    orig_lines = String.split(original, "\n")
    fmt_lines = String.split(formatted, "\n")

    ansi? = IO.ANSI.enabled?()
    red = if ansi?, do: IO.ANSI.red(), else: ""
    green = if ansi?, do: IO.ANSI.green(), else: ""
    reset = if ansi?, do: IO.ANSI.reset(), else: ""
    dim = if ansi?, do: IO.ANSI.faint(), else: ""

    info("#{dim}--- #{file} (original)#{reset}")
    info("#{dim}+++ #{file} (formatted)#{reset}")

    List.myers_difference(orig_lines, fmt_lines)
    |> Enum.each(fn
      {:eq, lines} ->
        Enum.each(lines, fn l -> IO.puts("#{dim} #{l}#{reset}") end)

      {:del, lines} ->
        Enum.each(lines, fn l -> IO.puts("#{red}-#{l}#{reset}") end)

      {:ins, lines} ->
        Enum.each(lines, fn l -> IO.puts("#{green}+#{l}#{reset}") end)
    end)
  end

  # v0.21.0: `cure fmt --check` runs through the algebra formatter so
  # it agrees with the new default. Falls back to the original source
  # internally when round-trip verification fails, so it never reports
  # a file as "needs formatting" solely because of a known-unsupported
  # layout edge case.
  defp fmt_check(files) do
    mismatched =
      Enum.filter(files, fn file ->
        source = File.read!(file)
        {:ok, formatted} = Cure.Compiler.Formatter.format_algebra(source)
        formatted != source
      end)

    case mismatched do
      [] ->
        info("All files are formatted")

      _ ->
        Enum.each(mismatched, fn file -> info("  needs formatting: #{file}") end)
        exit({:shutdown, 1})
    end
  end

  defp fmt_aggressive(files) do
    warn(
      "`cure fmt --aggressive` rewrites from the AST: plain `#` comments " <>
        "and non-canonical whitespace will be stripped. Make sure the target " <>
        "files are committed before continuing."
    )

    Enum.each(files, fn file ->
      source = File.read!(file)

      with {:ok, tokens} <- Cure.Compiler.Lexer.tokenize(source, file: file, emit_events: false),
           {:ok, ast} <- Cure.Compiler.Parser.parse(tokens, file: file, emit_events: false) do
        formatted = Cure.Compiler.Printer.quoted_to_string(ast)
        File.write!(file, formatted <> "\n")
        info("  formatted #{file}")
      else
        {:error, reason} ->
          error("  #{file}: #{inspect(reason)}")
      end
    end)
  end

  # -- watch ---------------------------------------------------------------------

  defp cmd_watch(paths, opts) do
    path = List.first(paths) || "."

    action =
      case Keyword.get(opts, :action, "compile") do
        "compile" -> :compile
        "check" -> :check
        "test" -> :test
        other -> String.to_atom(other)
      end

    watch_opts = [action: action]

    watch_opts =
      if v = Keyword.get(opts, :poll_ms), do: Keyword.put(watch_opts, :poll_ms, v), else: watch_opts

    watch_opts =
      if v = Keyword.get(opts, :debounce),
        do: Keyword.put(watch_opts, :debounce, v),
        else: watch_opts

    Cure.Watch.start(path, watch_opts)
  end

  # -- new -----------------------------------------------------------------------

  defp cmd_new([], _opts), do: error("Usage: cure new <name> [--lib | --app | --fsm]")

  defp cmd_new([name | _], opts) do
    template =
      cond do
        Keyword.get(opts, :app) -> :app
        Keyword.get(opts, :fsm) -> :fsm
        Keyword.get(opts, :lib) -> :lib
        Keyword.get(opts, :template) -> String.to_atom(Keyword.get(opts, :template))
        true -> :lib
      end

    Cure.Project.scaffold(name, template)
    IO.puts(Cure.CLI.NewMessage.render(name, template))
  end

  # -- bench ---------------------------------------------------------------------

  defp cmd_bench(paths, _opts) do
    files =
      case paths do
        [] -> Path.wildcard("bench/**/*.cure") ++ Path.wildcard("test/**/*_bench.cure")
        _ -> paths
      end

    if files == [] do
      info("No benchmark files found. Place benchmarks under bench/*.cure")
    else
      Enum.each(files, fn f ->
        case File.read(f) do
          {:ok, src} ->
            case Cure.Compiler.compile_and_load(src, file: f, emit_events: false) do
              {:ok, mod} ->
                exports = mod.module_info(:exports)

                bench_fns =
                  Enum.filter(exports, fn {n, a} ->
                    String.starts_with?(Atom.to_string(n), "bench") and a == 0
                  end)

                Enum.each(bench_fns, fn {name, _} ->
                  {us, _} = :timer.tc(fn -> apply(mod, name, []) end)
                  info("  #{f}:#{name}  #{us / 1000} ms")
                end)

              {:error, reason} ->
                error("  #{f}: #{inspect(reason)}")
            end

          {:error, reason} ->
            error("  #{f}: #{reason}")
        end
      end)
    end
  end

  # -- explain ------------------------------------------------------------------

  defp cmd_explain_all do
    entries = Cure.Compiler.Errors.list_all()
    code_width = entries |> Enum.map(fn {c, _, _} -> String.length(c) end) |> Enum.max(fn -> 4 end)

    info("Known error codes (run 'cure explain <code>' for full details):\n")

    Enum.each(entries, fn {code, title, brief} ->
      padded = String.pad_trailing(code, code_width)
      info("  #{padded}  #{title}")
      if brief != "", do: info("          #{brief}")
    end)
  end

  defp cmd_explain(code) do
    case Cure.Compiler.Errors.explain(code) do
      {:ok, text} -> info(text)
      :error -> error("Unknown error code: #{code}. Run 'cure explain' for a list.")
    end
  end

  # -- doctor -------------------------------------------------------------------

  defp cmd_doctor(_opts) do
    report = Cure.Doctor.run(".")
    _ = Cure.Doctor.render(report)

    unless report.ok?, do: exit({:shutdown, 1})
  end

  # -- fix ----------------------------------------------------------------------

  defp cmd_fix(opts) do
    dry? = Keyword.get(opts, :dry_run, false)
    results = Cure.Fix.run(".", dry_run: dry?)
    changed = Enum.filter(results, & &1.changed?)

    case {changed, dry?} do
      {[], _} ->
        info("cure fix: nothing to change.")

      {_, true} ->
        Enum.each(changed, fn r ->
          info("  would fix #{r.file}: #{Enum.join(Enum.map(r.applied, &Atom.to_string/1), ", ")}")
        end)

        exit({:shutdown, 1})

      {_, false} ->
        Enum.each(changed, fn r ->
          info("  fixed #{r.file}: #{Enum.join(Enum.map(r.applied, &Atom.to_string/1), ", ")}")
        end)

        info("cure fix: #{length(changed)} file(s) rewritten.")
    end
  end

  # -- publish / search / info -----------------------------------------------

  defp cmd_publish(opts) do
    if Keyword.get(opts, :registry) do
      Application.put_env(:cure, :registry_url, Keyword.get(opts, :registry))
    end

    cond do
      Keyword.get(opts, :hex, false) ->
        case Cure.Project.Publisher.build_hex_tarball(".") do
          {:ok, bytes} ->
            path = "_build/cure/publish/hex.tar"
            File.mkdir_p!(Path.dirname(path))
            File.write!(path, bytes)
            info("Hex-compatible tarball written to #{path}")
            info("Next: `mix hex.publish package --replace` with the tarball above.")

          {:error, reason} ->
            error("cure publish --hex failed: #{inspect(reason)}")
            exit({:shutdown, 1})
        end

      Keyword.get(opts, :dry_run, false) ->
        case Cure.Project.Publisher.build_tarball(".") do
          {:ok, bytes, sha, manifest} ->
            info("Would upload #{manifest["name"]} #{manifest["version"]}")
            info("  sha256 = #{sha}")
            info("  size   = #{byte_size(bytes)} bytes")
            info("  files  = #{length(Map.get(manifest, "dependencies", []))} declared deps")

          {:error, reason} ->
            error("cure publish --dry-run failed: #{inspect(reason)}")
            exit({:shutdown, 1})
        end

      true ->
        handle =
          Keyword.get(opts, :handle) ||
            System.get_env("CURE_HANDLE") ||
            prompt("Maintainer handle: ")

        token =
          Keyword.get(opts, :token) ||
            System.get_env("CURE_TOKEN") ||
            prompt("Upload token: ")

        case Cure.Project.Publisher.publish(".", handle, token) do
          {:ok, resp} ->
            info("Published: #{inspect(resp)}")

          {:error, reason} ->
            error("cure publish failed: #{inspect(reason)}")
            exit({:shutdown, 1})
        end
    end
  end

  defp cmd_search(query, opts) do
    if Keyword.get(opts, :registry) do
      Application.put_env(:cure, :registry_url, Keyword.get(opts, :registry))
    end

    case Cure.Project.Registry.search(query) do
      {:ok, hits} ->
        if hits == [] do
          info("No hits for '#{query}'.")
        else
          Enum.each(hits, fn h ->
            info("  #{Map.get(h, "name", "?")} #{Map.get(h, "version", "?")} -- #{Map.get(h, "description", "")}")
          end)
        end

      {:error, reason} ->
        error("cure search failed: #{inspect(reason)}")
        exit({:shutdown, 1})
    end
  end

  defp cmd_info(name_version, opts) do
    if Keyword.get(opts, :registry) do
      Application.put_env(:cure, :registry_url, Keyword.get(opts, :registry))
    end

    {name, maybe_version} =
      case String.split(name_version, ":", parts: 2) do
        [n, v] -> {n, v}
        [n] -> {n, nil}
      end

    case maybe_version do
      nil ->
        case Cure.Project.Registry.list_versions(name) do
          {:ok, versions} ->
            info("#{name}:")

            Enum.each(versions, fn v ->
              info("  #{v.version}  (sha256: #{v.sha256})")
            end)

          {:error, reason} ->
            error("cure info failed: #{inspect(reason)}")
            exit({:shutdown, 1})
        end

      v ->
        case Cure.Project.Registry.fetch_manifest(name, v) do
          {:ok, manifest} ->
            IO.puts(Cure.Project.Json.encode(manifest))

          {:error, reason} ->
            error("cure info failed: #{inspect(reason)}")
            exit({:shutdown, 1})
        end
    end
  end

  defp cmd_keys_generate(handle) do
    try do
      case Cure.Project.Signing.generate_keypair(handle) do
        {:ok, ^handle} -> info("Generated keypair for '#{handle}' under ~/.cure/keys/")
        other -> error("key generation returned unexpected: #{inspect(other)}")
      end
    rescue
      e -> error("key generation failed: #{Exception.message(e)}")
    end
  end

  # -- release ------------------------------------------------------------------

  defp cmd_release(_rest, opts) do
    case Cure.Project.load() do
      {:ok, project} ->
        release_opts =
          [
            include_erts: Keyword.get(opts, :include_erts, false),
            output_dir: Keyword.get(opts, :output_dir),
            overwrite: Keyword.get(opts, :overwrite, true)
          ]
          |> Enum.reject(fn {_k, v} -> is_nil(v) end)

        case Cure.Release.build(project, release_opts) do
          {:ok, dir} ->
            info("Release built: #{dir}")

          {:error, reason} ->
            error("cure release failed: #{inspect(reason)}")
            exit({:shutdown, 1})
        end

      {:error, :no_project_file} ->
        error("No Cure.toml found in current directory.")
        exit({:shutdown, 1})

      {:error, reason} ->
        error("cure release failed: #{inspect(reason)}")
        exit({:shutdown, 1})
    end
  end

  defp cmd_keys_list do
    trusted = Cure.Project.Signing.trusted_keys()

    if map_size(trusted) == 0 do
      info("No trusted keys. Generate one with `cure keys generate <handle>`.")
    else
      Enum.each(trusted, fn {h, pub} ->
        info("  #{h}  #{Base.encode16(pub, case: :lower) |> String.slice(0, 16)}...")
      end)
    end
  end

  defp prompt(msg) do
    IO.gets(msg) |> to_string() |> String.trim()
  end

  # -- version / help ----------------------------------------------------------

  defp cmd_version do
    IO.puts("Cure #{version()}")
  end

  defp help do
    IO.puts("""
    Cure #{version()} -- Dependently-typed language for the BEAM

    Usage: cure <command> [options] [arguments]

    Commands:
      compile <file|dir>   Compile .cure files to BEAM bytecode
      run <file>           Compile and execute a .cure file
      check <file>         Type-check without compiling
      lsp                  Start the Language Server Protocol server
      stdlib               Compile the standard library
      doc [path|dir]       Generate HTML documentation
      fmt [path|dir]       Format .cure source files (algebra by default; --safe, --aggressive, --check)
      repl                 Interactive Cure session (multi-line, :help for commands)
      watch [path]         Recompile/check/test on every save
      new <name>           Scaffold a new project (--lib | --app | --fsm)
      init <name>          Same as `new --lib`
      deps                 Resolve project dependencies
      test [--cover]       Run .cure tests under test/, optionally with coverage
      bench [path]         Run .cure benchmarks under bench/
      explain <Eddd>       Explain an error code
      why <Eddd>           Alias for `explain`
      doctor               Environment + project + source health report
      fix [--dry-run]      Apply safe project-wide code fixes
      publish [opts]       Package and upload to the Cure registry
      search <query>       Search the registry for packages
      info <name[:ver]>    Show registry manifest / version list
      keys generate <h>    Generate an Ed25519 signing keypair
      keys list            List trusted publisher keys
      release              Build a BEAM release (requires `app`)
      top                  Print a runtime snapshot (supervisors / actors / FSMs)
      trace <M.f/a>        Typed tracer over :dbg (--duration N)
      synth                Synthesise typed-hole candidates (--goal T --ctx x=T)
      john                 Print everything: VM stats, tooling, project, logs
      version              Show version
      help                 Show this help

    Options:
      -o, --output-dir DIR   Output directory (default: _build/cure/ebin)
      --no-type-check        Skip the type checker (compile/run only; check
                             always type-checks). Type checking is ON by default.
      --optimize             Enable optimization passes
      --action ACTION        Watch action: compile (default) | check | test
      --poll-ms N            Watch poll interval (default 500)
      --debounce N           Watch coalesce window (default 200)
      --lib | --app | --fsm  `cure new` template selector
      --filter PATTERN       `cure test` filter
      --doctests             `cure test` includes doctests
      --cover                `cure test --cover` emits _build/cure/cover/index.html
      --dry-run              `cure fix --dry-run`, `cure publish --dry-run`
      --hex                  `cure publish --hex` -- Hex-compatible tarball
      --handle HANDLE        Maintainer handle for `cure publish`
      --token TOKEN          Upload token for `cure publish`
      --registry URL         Override registry base URL
      --include-erts         `cure release --include-erts` bundles ERTS
      --overwrite            `cure release --overwrite` wipes output dir (default)
      -v, --verbose          Verbose output
      -h, --help             Show help
    """)
  end

  # -- verify (v0.32.0) ---------------------------------------------------------

  defp cmd_verify(rest, opts) do
    strict? = Keyword.get(opts, :strict, false)
    path = List.first(rest)

    Mix.Tasks.Cure.Verify.run(
      if(strict?, do: ["--strict"], else: []) ++
        if(path, do: [path], else: [])
    )
  end

  # -- export-types (v0.32.0) ---------------------------------------------------

  defp cmd_export_types(rest, opts) do
    target = Keyword.get(opts, :target, "protobuf")
    out = Keyword.get(opts, :out)
    verbose? = Keyword.get(opts, :verbose, false)

    cli_args =
      ["--target", target] ++
        if(out, do: ["--out", out], else: []) ++
        if(verbose?, do: ["--verbose"], else: []) ++
        rest

    Mix.Tasks.Cure.ExportTypes.run(cli_args)
  end

  # -- snap (v0.32.0) -----------------------------------------------------------

  defp cmd_snap([], _opts) do
    IO.puts(:stderr, "Usage: cure snap <save|load|list> [options]")
    exit({:shutdown, 1})
  end

  defp cmd_snap([sub | rest], opts) do
    out = Keyword.get(opts, :out)

    cli_args =
      [sub] ++
        if(out, do: ["--out", out], else: []) ++
        rest

    Mix.Tasks.Cure.Snap.run(cli_args)
  end

  # -- story (v0.32.0) ----------------------------------------------------------

  defp cmd_story(opts) do
    out = Keyword.get(opts, :out)
    stdout? = Keyword.get(opts, :verbose, false)
    diagrams? = false

    cli_args =
      if(out, do: ["--out", out], else: []) ++
        if(stdout?, do: ["--stdout"], else: []) ++
        if diagrams?, do: ["--diagrams"], else: []

    Mix.Tasks.Cure.Story.run(cli_args)
  end

  # -- Output helpers ----------------------------------------------------------

  defp info(msg), do: IO.puts(msg)
  defp warn(msg), do: IO.puts(:stderr, "warning: #{msg}")
  defp error(msg), do: IO.puts(:stderr, "error: #{msg}")

  # Print a pre-formatted multi-line diagnostic (e.g. from
  # `Cure.Compiler.Errors`) verbatim. The string already contains its own
  # `error: <category>` header, so avoid the extra prefix from `error/1`.
  defp diagnostic(msg), do: IO.puts(:stderr, msg)
end
