defmodule Mix.Tasks.Cure.Check.Stdlib do
  @moduledoc """
  Regression task: compiles every `.cure` file in `lib/std/` and fails
  if any module fails to produce a `.beam` or emits a compiler warning.

  Invoke as:

      mix cure.check.stdlib

  This is intentionally stricter than `mix cure.compile_stdlib`:

  - any error is fatal,
  - any warning is fatal too (the stdlib must be warning-free so
    downstream programs can rely on clean `erl_lint` output).

  CI consumes the exit code to gate merges.
  """

  use Mix.Task

  @shortdoc "Compile every Std.* module and reject errors or warnings"

  @stdlib_dir "lib/std"
  @output_dir "_build/cure/ebin"

  @impl Mix.Task
  def run(_args) do
    Application.ensure_all_started(:cure)
    files = Path.wildcard(Path.join(@stdlib_dir, "*.cure")) |> Enum.sort()

    results =
      Enum.map(files, fn path ->
        name = Path.basename(path, ".cure")

        case Cure.Compiler.compile_file(path, output_dir: @output_dir, emit_events: false) do
          {:ok, module, []} ->
            IO.puts("  ok  #{pad(name)} -> #{module}")
            {:pass, name}

          {:ok, _module, warnings} ->
            msg = "#{length(warnings)} warning(s): #{inspect(warnings)}"
            IO.puts("  FAIL #{pad(name)} #{msg}")
            {:fail, name, msg}

          {:error, reason} ->
            msg = "compile error: #{inspect(reason)}"
            IO.puts("  FAIL #{pad(name)} #{msg}")
            {:fail, name, msg}
        end
      end)

    passed = Enum.count(results, &match?({:pass, _}, &1))
    failed = Enum.filter(results, &match?({:fail, _, _}, &1))

    if failed == [] do
      IO.puts("\nstdlib: #{passed} passed, 0 failed")
      :ok
    else
      IO.puts("\nstdlib: #{passed} passed, #{length(failed)} failed")
      exit({:shutdown, 1})
    end
  end

  defp pad(name), do: String.pad_trailing(name, 20)
end
