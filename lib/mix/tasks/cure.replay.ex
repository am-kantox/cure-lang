defmodule Mix.Tasks.Cure.Replay do
  @shortdoc "Replay a recorded FSM trace from a .journal file"

  @moduledoc """
  Replay a recorded FSM/actor trace produced by a `@record`-annotated container.

  Journal files are written to `.cure-trace/` by `Cure.Observe.Journal.flush/1`
  when the decorated process terminates, or by calling `flush/1` manually.

  ## Usage

      mix cure.replay .cure-trace/abc123.journal [--module MyFsm] [--step]

  If `--module` is omitted, the replay only prints the trace without
  live replay (useful for inspection).

  ## Options

    * `--module` / `-m` -- the FSM module to replay against
    * `--step`   / `-s` -- pause after each event (single-step mode)
    * `--print`         -- print the trace before replaying (default: true)

  """

  use Mix.Task

  @impl Mix.Task
  def run(args) do
    Application.ensure_all_started(:cure)

    {opts, rest, _} =
      OptionParser.parse(args,
        switches: [module: :string, step: :boolean, print: :boolean],
        aliases: [m: :module, s: :step]
      )

    path = List.first(rest)

    if is_nil(path) do
      Mix.Shell.IO.error("Usage: mix cure.replay <path.journal> [--module ModuleName] [--step]")
      exit({:shutdown, 1})
    end

    case Cure.Observe.Journal.load(path) do
      {:error, reason} ->
        Mix.Shell.IO.error("Cannot load #{path}: #{inspect(reason)}")
        exit({:shutdown, 1})

      {:ok, entries} ->
        Mix.Shell.IO.info("Loaded #{length(entries)} journal entries from #{path}")

        if Keyword.get(opts, :print, true) do
          Mix.Shell.IO.info("\nTrace:")
          Cure.Observe.Replay.print_trace(entries)
        end

        case Keyword.get(opts, :module) do
          nil ->
            Mix.Shell.IO.info("\n(pass --module ModuleName to replay against a live FSM)")

          mod_str ->
            mod = Module.concat([mod_str])

            if Code.ensure_loaded?(mod) do
              step? = Keyword.get(opts, :step, false)
              Mix.Shell.IO.info("\nReplaying against #{mod_str}#{if step?, do: " (step mode)", else: ""}...")

              case Cure.Observe.Replay.replay(mod, entries, step: step?) do
                {:ok, :quit} ->
                  Mix.Shell.IO.info("Replay quit early.")

                {:ok, results} ->
                  ok = Enum.count(results, fn {_, _, _, outcome} -> outcome == :ok end)
                  warn = length(results) - ok
                  Mix.Shell.IO.info("Replay complete: #{ok} ok, #{warn} warnings.")

                {:error, reason} ->
                  Mix.Shell.IO.error("Replay failed: #{inspect(reason)}")
                  exit({:shutdown, 1})
              end
            else
              Mix.Shell.IO.error("Module #{mod_str} is not loaded. Compile the project first.")
              exit({:shutdown, 1})
            end
        end
    end
  end
end
