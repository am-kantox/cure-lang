defmodule Mix.Tasks.Cure.Profile do
  @moduledoc """
  Profile the compilation of a Cure source file.

  Shows timing data per pipeline stage and event counts.

  ## Usage

      mix cure.profile path/to/file.cure
  """

  use Mix.Task

  @shortdoc "Profile compilation of a Cure source file"

  @impl Mix.Task
  def run(args) do
    Mix.Task.run("app.start", [])

    case args do
      [path | _] ->
        case Cure.Profiler.profile_file(path) do
          {:ok, report} -> IO.puts(Cure.Profiler.format_report(report))
          {:error, reason} -> Mix.shell().error("Error: #{inspect(reason)}")
        end

      [] ->
        Mix.shell().error("Usage: mix cure.profile <file.cure>")
    end
  end
end
