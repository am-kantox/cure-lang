defmodule Mix.Tasks.Cure.CompileStdlib do
  @moduledoc """
  Compiles the Cure standard library from `lib/std/*.cure` to BEAM bytecode.

  The compiled `.beam` files are placed in `_build/cure/ebin/` (or the
  directory given by `--output-dir`) and added to the Erlang code path so
  they can be used by Cure programs at runtime.

  ## Usage

      mix cure.compile_stdlib
      mix cure.compile_stdlib --output-dir path/to/ebin
  """

  use Mix.Task

  @shortdoc "Compiles the Cure standard library"

  @impl Mix.Task
  def run(args) do
    {opts, _, _} =
      OptionParser.parse(args,
        switches: [output_dir: :string],
        aliases: [o: :output_dir]
      )

    output_dir = Keyword.get(opts, :output_dir, "_build/cure/ebin")

    # Ensure the application is started (for Registry)
    Mix.Task.run("app.start", [])

    stdlib_dir = Path.join(["lib", "std"])
    cure_files = Path.wildcard(Path.join(stdlib_dir, "*.cure")) |> Enum.sort()

    if cure_files == [] do
      Mix.shell().info("No .cure files found in #{stdlib_dir}")
      :ok
    else
      Mix.shell().info("Compiling Cure standard library (#{length(cure_files)} modules)")

      results =
        Enum.map(cure_files, fn path ->
          name = Path.basename(path, ".cure")
          Mix.shell().info("  #{name}")

          case Cure.Compiler.compile_file(path, output_dir: output_dir, emit_events: false) do
            {:ok, module, warnings} ->
              Enum.each(warnings, fn w ->
                Mix.shell().info("    warning: #{inspect(w)}")
              end)

              {:ok, module}

            {:error, reason} ->
              formatted = Cure.Compiler.Errors.format_error(reason, path)
              Mix.shell().error("    #{formatted}")
              {:error, path}
          end
        end)

      # Add to code path
      File.mkdir_p!(output_dir)
      abs_dir = Path.expand(output_dir)

      unless abs_dir in :code.get_path() do
        :code.add_patha(String.to_charlist(abs_dir))
      end

      ok_count = Enum.count(results, &match?({:ok, _}, &1))
      err_count = Enum.count(results, &match?({:error, _}, &1))

      Mix.shell().info("  #{ok_count} compiled, #{err_count} errors")
      Mix.shell().info("  Output: #{output_dir}")

      if err_count > 0 do
        exit({:shutdown, 1})
      end
    end
  end
end
