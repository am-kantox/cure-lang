defmodule Mix.Tasks.CompileCure do
  @moduledoc """
  Compiles `.cure` source files for the Cure motif example.

  The Cure actor, supervisor, FSM, and app compilers load their generated
  modules eagerly via `Code.compile_string/2` or `:compile.forms/2`; some
  containers emit a `.beam` under `_build/cure/ebin/`, others stay
  memory-resident. In either case the Mix task needs to run before the
  Elixir compile step (and before each test run) so every compiled module is
  live in the VM when the application supervisor starts.

  Actor and FSM containers have no forward references between files, so
  compile order matters only for readability. We compile the pure module
  first (it is the biggest and all other files refer to its types),
  then the FSM, the actor containers, the supervisor, and finally the app
  container.
  """

  use Mix.Task

  @shortdoc "Compiles .cure source files for cure_motif"

  @cure_src "cure_src"
  @output_dir "_build/cure/ebin"

  @preferred_order [
    "motif.cure",
    "envelope.cure",
    "voice.cure",
    "sequencer.cure",
    "clock.cure",
    "orchestra.cure",
    "motif_app.cure"
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

      # The Cure standard library is compiled by the root `:cure`
      # project into `<cure_root>/_build/cure/ebin`, not into the
      # consumer's `_build/cure/ebin`. Add it to the code path so
      # modules like `:"Cure.Std.Vector"` resolve at runtime.
      stdlib_ebin = Path.expand("../../_build/cure/ebin")

      if File.dir?(stdlib_ebin) and stdlib_ebin not in :code.get_path() do
        :code.add_patha(~c"#{stdlib_ebin}")
      end

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
