defmodule Mix.Tasks.CompileCure do
  @moduledoc """
  Compiles `.cure` source files for the Cure forge example.

  The Cure actor, supervisor, and app compilers load their generated
  modules eagerly via `Code.compile_string/2`; no `.beam` file is
  written to disk for those containers. The task therefore needs to
  run before the Elixir compile step (and before each test run) so
  the `Cure.Actor.*`, `Cure.Sup.*`, and `Cure.App.*` modules are live
  in the VM when the application supervisor starts.

  Ordering matters at runtime, not at compile time: the
  `Cure.Sup.Forge.Root` child specs reference `Cure.Actor.Metrics`,
  `Cure.Actor.Logger`, `Cure.Actor.Queue`, and `Cure.Actor.Pool` as
  atoms, so compile order is irrelevant. Still, we compile actors
  first for clarity, then the supervisor, then the application
  container.
  """

  use Mix.Task

  @shortdoc "Compiles .cure source files for cure_forge"

  @cure_src "cure_src"
  @output_dir "_build/cure/ebin"

  # Actors first, supervisor in the middle, app container last. Any
  # file not listed here is compiled after the named ones in
  # alphabetical order.
  @preferred_order [
    "metrics.cure",
    "logger.cure",
    "queue.cure",
    "pool.cure",
    "forge_root.cure",
    "forge_app.cure"
  ]

  @impl Mix.Task
  def run(_args) do
    cure_files =
      Path.wildcard(Path.join(@cure_src, "**/*.cure"))
      |> Enum.sort_by(&order_key/1)

    if cure_files != [] do
      File.mkdir_p!(@output_dir)
      ebin = Path.expand(@output_dir)

      unless ebin in :code.get_path() do
        :code.add_patha(~c"#{ebin}")
      end

      Application.ensure_all_started(:cure)

      Enum.each(cure_files, fn path ->
        case Cure.Compiler.compile_file(path,
               output_dir: @output_dir,
               emit_events: false,
               check_types: false
             ) do
          {:ok, module, _warnings} ->
            Mix.shell().info("Compiled #{path} -> #{module}")

          {:error, reason} ->
            Mix.shell().error("Failed to compile #{path}: #{inspect(reason)}")
        end
      end)
    end
  end

  defp order_key(path) do
    basename = Path.basename(path)

    case Enum.find_index(@preferred_order, &(&1 == basename)) do
      nil -> {1, basename}
      idx -> {0, idx}
    end
  end
end
