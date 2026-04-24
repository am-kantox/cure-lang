defmodule Mix.Tasks.Cure.John do
  @shortdoc "Print an everything-in-one-shot diagnostic of Cure and the VM"

  @moduledoc """
  Panoramic diagnostic for the Cure toolchain, the BEAM VM it is riding
  on, and the project currently in `pwd`.

  Produces a single, structured, Markdown-rendered report covering:

    * Cure -- version, loaded stdlib modules, protocol registry, event bus
    * BEAM / OTP -- scheduler topology, memory, process / atom / port
      counts, uptime
    * System -- OS, architecture, hostname, environment variables
    * Tooling -- Elixir / OTP / Cure, Z3 / git / make availability, loaded
      dependency versions
    * Project -- `Cure.toml` fields, dependency table, lockfile status
      (when `pwd` contains a Cure project)
    * Runtime -- `Cure.Observe.Top` snapshot when Cure is started
    * Doctor -- severity counters from `Cure.Doctor.run/1`
    * Recent logs -- tails of `.cure/logs/` and `_build/cure/logs/`

  Named in tribute to **John Carbajal** -- the teammate who made dashboards
  worth looking at.

  ## Usage

      mix cure.john
      mix cure.john --width 100
      mix cure.john --no-ansi
      mix cure.john --no-banner

  ## Options

    * `--width N` -- target width for separators (default 80)
    * `--ansi` / `--no-ansi` -- force ANSI rendering on or off
    * `--banner` / `--no-banner` -- show or hide the dedication banner
    * `--root PATH` -- treat `PATH` as the project root (default `cwd`)
  """

  use Mix.Task

  @impl Mix.Task
  def run(args) do
    Application.ensure_all_started(:cure)

    {opts, _, _} =
      OptionParser.parse(args,
        switches: [width: :integer, ansi: :boolean, banner: :boolean, root: :string]
      )

    run_opts =
      opts
      |> Keyword.take([:width, :banner, :root])
      |> Keyword.merge(ansi_opt(opts))

    _ = Cure.John.run(run_opts)
    :ok
  end

  defp ansi_opt(opts) do
    case Keyword.fetch(opts, :ansi) do
      {:ok, value} -> [ansi: value]
      :error -> []
    end
  end
end
