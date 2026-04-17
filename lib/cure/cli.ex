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

  @version Mix.Project.config()[:version]

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
          check: :boolean
        ],
        aliases: [o: :output_dir, v: :verbose, h: :help, f: :filter, t: :template]
      )

    if opts[:help] do
      help()
    else
      case rest do
        ["compile" | paths] -> cmd_compile(paths, opts)
        ["run" | [path]] -> cmd_run(path, opts)
        ["check" | [path]] -> cmd_check(path, opts)
        ["lsp"] -> cmd_lsp()
        ["stdlib"] -> cmd_stdlib(opts)
        ["version"] -> cmd_version()
        ["init" | [name]] -> cmd_init(name)
        ["deps"] -> cmd_deps()
        ["deps", "update"] -> cmd_deps_update()
        ["deps", "tree"] -> cmd_deps_tree()
        ["test"] -> cmd_test(opts)
        ["explain" | [code]] -> cmd_explain(code)
        ["doc" | paths] -> cmd_doc(paths, opts)
        ["repl"] -> cmd_repl()
        ["fmt" | paths] -> cmd_fmt(paths, opts)
        ["watch" | rest] -> cmd_watch(rest, opts)
        ["new" | rest] -> cmd_new(rest, opts)
        ["bench" | rest] -> cmd_bench(rest, opts)
        ["why" | [code]] -> cmd_explain(code)
        ["help"] -> help()
        [] -> help()
        [unknown | _] -> error("Unknown command: #{unknown}. Run 'cure help' for usage.")
      end
    end
  end

  # -- compile -----------------------------------------------------------------

  defp cmd_compile([], _opts), do: error("Usage: cure compile <file|directory>")

  defp cmd_compile(paths, opts) do
    output_dir = Keyword.get(opts, :output_dir, "_build/cure/ebin")
    check? = Keyword.get(opts, :type_check, true)
    optimize? = Keyword.get(opts, :optimize, false)
    verbose? = Keyword.get(opts, :verbose, false)

    compile_opts = [
      output_dir: output_dir,
      check_types: check?,
      optimize: optimize?,
      emit_events: false
    ]

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

  defp cmd_run(path, opts) do
    # Type checking runs by default; use `--no-type-check` to opt out.
    check? = Keyword.get(opts, :type_check, true)
    optimize? = Keyword.get(opts, :optimize, false)

    preload_stdlib()

    source =
      case File.read(path) do
        {:ok, s} -> s
        {:error, reason} -> error("Cannot read #{path}: #{reason}") && exit({:shutdown, 1})
      end

    case Cure.Compiler.compile_and_load(source,
           file: path,
           check_types: check?,
           optimize: optimize?,
           emit_events: false
         ) do
      {:ok, module} ->
        if function_exported?(module, :main, 0) do
          result = module.main()
          if result != :ok and result != nil, do: IO.inspect(result)
        else
          info("Module #{module} compiled (no main/0 function)")
        end

      {:error, reason} ->
        formatted = Cure.Compiler.Errors.format_error(reason, path)
        diagnostic(formatted)
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
    Cure.Stdlib.Preload.preload(examples: true)
  end

  # -- check -------------------------------------------------------------------

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
        info("Resolving dependencies for #{project.name}...")
        Cure.Project.resolve_deps(project)
        Cure.Project.write_lock(project)
        info("Dependencies resolved. Cure.lock written.")

      {:error, :no_project_file} ->
        error("No Cure.toml found in current directory.")

      {:error, reason} ->
        error("Error: #{inspect(reason)}")
    end
  end

  defp cmd_deps_update do
    case Cure.Project.load() do
      {:ok, project} ->
        info("Updating dependencies for #{project.name}...")

        Enum.each(project.dependencies, fn dep ->
          if Map.get(dep, :git) do
            Cure.Project.resolve_git_dep(dep, project.root)
          end
        end)

        Cure.Project.write_lock(project)
        info("Lockfile updated.")

      {:error, reason} ->
        error("Error: #{inspect(reason)}")
    end
  end

  defp cmd_deps_tree do
    case Cure.Project.load() do
      {:ok, project} ->
        IO.puts(Cure.Project.dep_tree(project))

      {:error, reason} ->
        error("Error: #{inspect(reason)}")
    end
  end

  # -- test --------------------------------------------------------------------

  defp cmd_test(opts) do
    filter = Keyword.get(opts, :filter, nil)
    doctests? = Keyword.get(opts, :doctests, false)
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
      if fail > 0, do: exit({:shutdown, 1})
    end
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

  defp cmd_doc(paths, opts) do
    output_dir = Keyword.get(opts, :output_dir, "_build/cure/doc")
    title = Keyword.get(opts, :title, "Cure Documentation")

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

      Cure.Doc.HTMLGenerator.generate(modules, output_dir, title: title)
      info("Documentation written to #{output_dir}/ (#{length(modules)} modules)")
    end
  end

  # -- repl --------------------------------------------------------------------

  defp cmd_repl do
    Cure.REPL.start()
  end

  # -- fmt ---------------------------------------------------------------------

  # Two modes:
  #
  #   * (default) safe, source-preserving formatter. Runs
  #     `Cure.Compiler.Formatter`, which normalises line endings,
  #     trailing whitespace, leading-tab indentation, blank-line runs,
  #     and operator spacing. Plain `#` comments, string literals,
  #     regex bodies, and doc comments are preserved byte-for-byte.
  #     Every rewrite is round-trip-validated against the original
  #     AST before being written to disk.
  #
  #   * `--aggressive` / `--ast`: canonicalising AST pretty printer.
  #     Reformats the buffer from the parse tree, which strips plain
  #     `#` comments and any layout that doesn't survive a parser
  #     round-trip. The command prints a banner before touching disk
  #     so users know what they're opting into.
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

      Keyword.get(opts, :check, false) ->
        fmt_check(cure_files)

      true ->
        fmt_safe(cure_files)
    end
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

  defp fmt_check(files) do
    mismatched =
      Enum.filter(files, fn file ->
        source = File.read!(file)
        {:ok, formatted} = Cure.Compiler.Formatter.format(source)
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
    info("Created project '#{name}' (template: #{template})")
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

  defp cmd_explain(code) do
    case Cure.Compiler.Errors.explain(code) do
      {:ok, text} -> info(text)
      :error -> error("Unknown error code: #{code}. Run 'cure explain' for a list.")
    end
  end

  # -- version / help ----------------------------------------------------------

  defp cmd_version do
    IO.puts("Cure #{@version}")
  end

  defp help do
    IO.puts("""
    Cure #{@version} -- Dependently-typed language for the BEAM

    Usage: cure <command> [options] [arguments]

    Commands:
      compile <file|dir>   Compile .cure files to BEAM bytecode
      run <file>           Compile and execute a .cure file
      check <file>         Type-check without compiling
      lsp                  Start the Language Server Protocol server
      stdlib               Compile the standard library
      doc [path|dir]       Generate HTML documentation
      fmt [path|dir]       Format .cure source files
      repl                 Interactive Cure session (multi-line, :help for commands)
      watch [path]         Recompile/check/test on every save
      new <name>           Scaffold a new project (--lib | --app | --fsm)
      init <name>          Same as `new --lib`
      deps                 Resolve project dependencies
      test                 Run .cure tests under test/
      bench [path]         Run .cure benchmarks under bench/
      explain <Eddd>       Explain an error code
      why <Eddd>           Alias for `explain`
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
      -v, --verbose          Verbose output
      -h, --help             Show help
    """)
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
