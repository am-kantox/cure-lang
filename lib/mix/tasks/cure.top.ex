defmodule Mix.Tasks.Cure.Top do
  @moduledoc """
  Print an observability snapshot of the running Cure system.

  ## Usage

      mix cure.top
      mix cure.top --width 120
      watch -n1 mix cure.top

  The task captures a point-in-time snapshot of supervisors, actors,
  and FSMs and renders it to stdout. Pair with `watch` (or `entr`)
  for a low-tech live view.
  """

  use Mix.Task

  @shortdoc "Print a Cure.Observe.Top snapshot"

  @impl Mix.Task
  def run(args) do
    Application.ensure_all_started(:cure)

    {opts, _, _} =
      OptionParser.parse(args, switches: [width: :integer])

    width = Keyword.get(opts, :width, 80)

    snapshot = Cure.Observe.Top.snapshot()
    rendered = Cure.Observe.Top.render(snapshot, width: width)

    IO.puts(rendered)
  end
end
