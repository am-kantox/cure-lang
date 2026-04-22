defmodule Mix.Tasks.Cure.Bless do
  @shortdoc "Interactively walk through type errors and offer fixes"

  @moduledoc """
  Socratic type-error assistant.

  For each type error in the given `.cure` file, `cure bless` displays
  the error, explains what went wrong, and offers a concrete fix with a
  `[y/n/s]` prompt.

  ## Usage

      mix cure.bless path/to/file.cure

  ## Options

    * `--no-interactive` / `--batch` -- print suggestions without
      prompting. Useful in CI to preview what bless would do.

  """

  use Mix.Task

  @impl Mix.Task
  def run(args) do
    Application.ensure_all_started(:cure)

    {opts, rest, _} =
      OptionParser.parse(args,
        switches: [interactive: :boolean, batch: :boolean],
        aliases: [b: :batch]
      )

    interactive? = not (Keyword.get(opts, :batch, false) or not Keyword.get(opts, :interactive, true))

    case rest do
      [] ->
        Mix.Shell.IO.error("Usage: mix cure.bless path/to/file.cure")

      paths ->
        Enum.each(paths, fn path ->
          Mix.Shell.IO.info("Blessing #{path}...")

          case Cure.Bless.bless_file(path, interactive: interactive?) do
            :nothing_to_fix ->
              Mix.Shell.IO.info("  No type errors found.")

            :all_fixed ->
              Mix.Shell.IO.info("  All errors fixed.")

            :some_skipped ->
              Mix.Shell.IO.info("  Some errors remain (skipped or declined).")

            {:error, reason} ->
              Mix.Shell.IO.error("  Error: #{reason}")
          end
        end)
    end
  end
end
