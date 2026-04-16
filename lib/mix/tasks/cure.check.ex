defmodule Mix.Tasks.Cure.Check do
  @moduledoc """
  Run every Cure regression check in sequence:

      mix cure.check

  Currently dispatches to:

  - `mix cure.check.stdlib`   -- every `lib/std/*.cure` compiles
                                 without warnings.
  - `mix cure.check.examples` -- every `examples/*.cure` compiles,
                                 and those with `fn main/0` produce
                                 the expected output.

  Exits non-zero on the first failure so CI can gate merges.
  """

  use Mix.Task

  @shortdoc "Run every Cure regression check"

  @impl Mix.Task
  def run(args) do
    IO.puts("== cure.check.stdlib ==")
    Mix.Task.run("cure.check.stdlib", args)

    IO.puts("\n== cure.check.examples ==")
    Mix.Task.run("cure.check.examples", args)

    IO.puts("\nAll Cure regression checks passed.")
    :ok
  end
end
