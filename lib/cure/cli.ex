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
          help: :boolean
        ],
        aliases: [o: :output_dir, v: :verbose, h: :help]
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
        ["test"] -> cmd_test(opts)
        ["explain" | [code]] -> cmd_explain(code)
        ["doc" | paths] -> cmd_doc(paths, opts)
        ["repl"] -> cmd_repl()
        ["fmt" | paths] -> cmd_fmt(paths)
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
        error(formatted)
    end
  end

  # -- run ---------------------------------------------------------------------

  defp cmd_run(path, opts) do
    check? = Keyword.get(opts, :type_check, false)
    optimize? = Keyword.get(opts, :optimize, false)

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
        error(formatted)
        exit({:shutdown, 1})
    end
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
        formatted = Cure.Compiler.Errors.format_error(reason, path)
        error(formatted)
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
        info("Dependencies resolved.")

      {:error, :no_project_file} ->
        error("No Cure.toml found in current directory.")

      {:error, reason} ->
        error("Error: #{inspect(reason)}")
    end
  end

  # -- test --------------------------------------------------------------------

  defp cmd_test(_opts) do
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
                Enum.filter(exports, fn {name, arity} ->
                  String.starts_with?(Atom.to_string(name), "test") and arity == 0
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
    info("Cure REPL v#{@version} (type :quit to exit)")
    repl_loop(1)
  end

  defp repl_loop(n) do
    case IO.gets("cure(#{n})> ") do
      :eof ->
        :ok

      {:error, _} ->
        :ok

      line ->
        line = String.trim(line)

        cond do
          line in [":quit", ":q", ":exit"] ->
            info("Bye.")

          line == "" ->
            repl_loop(n)

          true ->
            mod_name = "Repl.M#{n}"

            source = """
            mod #{mod_name}
              fn main() -> Any = #{line}
            """

            case Cure.Compiler.compile_and_load(source, emit_events: false) do
              {:ok, module} ->
                try do
                  result = module.main()
                  IO.inspect(result)
                catch
                  kind, reason ->
                    error("#{kind}: #{inspect(reason)}")
                end

              {:error, reason} ->
                error(inspect(reason))
            end

            repl_loop(n + 1)
        end
    end
  end

  # -- fmt ---------------------------------------------------------------------

  defp cmd_fmt(paths) do
    cure_files =
      case paths do
        [] ->
          Path.wildcard("lib/**/*.cure") ++ Path.wildcard("test/**/*.cure")

        _ ->
          Enum.flat_map(paths, fn p ->
            if File.dir?(p), do: Path.wildcard(Path.join(p, "**/*.cure")), else: [p]
          end)
      end

    Enum.each(cure_files, fn file ->
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
      repl                 Interactive Cure session
      version              Show version
      help                 Show this help

    Options:
      -o, --output-dir DIR   Output directory (default: _build/cure/ebin)
      --no-type-check        Skip type checking
      --optimize             Enable optimization passes
      -v, --verbose          Verbose output
      -h, --help             Show help
    """)
  end

  # -- Output helpers ----------------------------------------------------------

  defp info(msg), do: IO.puts(msg)
  defp warn(msg), do: IO.puts(:stderr, "warning: #{msg}")
  defp error(msg), do: IO.puts(:stderr, "error: #{msg}")
end
