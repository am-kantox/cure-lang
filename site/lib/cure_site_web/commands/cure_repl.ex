defmodule CureSiteWeb.Commands.CureRepl do
  @moduledoc """
  Yeesh command wrapper around the `mix cure.repl` Mix task.

  Launches a fully-featured Cure REPL session inside the Yeesh
  terminal. Because the browser terminal has no controlling tty, we
  disable raw-mode editing (`--no-raw`), route compiler diagnostics
  through the task's group leader (`--error-device=stdio`), and skip
  history persistence (`--no-history`). The REPL therefore falls back
  to its `IO.gets`-driven legacy loop, which `Yeesh.IOServer`
  transparently intercepts so every `IO.gets` prompt becomes an
  interactive exchange with the browser.

  ## Usage

      repl                         # start an interactive Cure session
      repl --theme=light           # override the default theme

  Pass `:quit` (or `:q`, `:exit`) inside the REPL to leave the session.
  Typing a bare `exit` at the Yeesh prompt while in `:mix_task` mode
  also kills the task.
  """

  use Yeesh.MixCommand,
    task: "cure.repl",
    name: "repl",
    description: "Launch an interactive Cure REPL session",
    usage:
      "repl [--theme=dark|light|mono] [--mode=emacs|vi]\n" <>
        "                       - interactive Cure session (:help inside)",
    default_args: [
      "--no-raw",
      "--error-device=stdio",
      "--no-history",
      "--theme=dark"
    ]

  @doc """
  The Yeesh MixCommand macro doesn't install a default `group/0`; we
  bucket this command next to `eval` under the "Cure" heading so the
  `help` output keeps both Cure affordances together.
  """
  @impl Yeesh.Command
  def group, do: "Cure"

  @doc """
  Offer static completions for the common option flags so the terminal's
  Tab key is useful before the REPL session starts.
  """
  @impl Yeesh.Command
  def completions(partial, _session) do
    ~w(
      --theme=dark
      --theme=light
      --theme=mono
      --mode=emacs
      --mode=vi
      --no-history
      --error-device=stdio
      --error-device=stderr
    )
    |> Enum.filter(&String.starts_with?(&1, partial))
  end
end
