defmodule CureSiteWeb.Commands.CureRepl do
  @moduledoc """
  Yeesh command that launches a full Cure REPL inside the browser
  terminal.

  ## Architecture

  Historically this command was implemented via `Yeesh.MixCommand`,
  which shells out to the `cure.repl` Mix task under a
  `Yeesh.IOServer` group leader. That worked in development but
  crashed inside a `MIX_ENV=prod` release -- Mix is intentionally
  absent from the release application list, so every call that
  reached `Mix.Task.get/1` raised.

  The command now bypasses Mix entirely at runtime:

    * Argument parsing lives in `Cure.REPL.Options`, shared verbatim
      with `Mix.Tasks.Cure.Repl`.
    * Execution runs through `CureSiteWeb.Yeesh.CallableRunner`,
      which plays the same `Yeesh.IOServer`-as-group-leader trick as
      `Yeesh.MixRunner` but targets an arbitrary 0-arity function
      instead of a Mix task.
    * The REPL itself is launched by calling `Cure.REPL.start/1`
      directly.

  Because the REPL hands control over to the browser via
  `IO.gets`, the command defaults to `--no-raw`, `--error-device=stdio`,
  and `--no-history` (same defaults as before) so the legacy line-mode
  loop activates and compiler diagnostics land in the xterm buffer.

  ## Usage

      repl                         # start an interactive Cure session
      repl --theme=light           # override the default theme

  Pass `:quit` (or `:q`, `:exit`) inside the REPL to leave the session.
  Typing a bare `exit` at the Yeesh prompt while in `:mix_task` mode
  also kills the task.
  """

  @behaviour Yeesh.Command

  alias Cure.REPL.Options
  alias CureSiteWeb.Yeesh.CallableRunner

  @default_args ~w(
    --no-raw
    --error-device=stdio
    --no-history
    --theme=dark
  )

  @completion_hints ~w(
    --theme=dark
    --theme=light
    --theme=mono
    --mode=emacs
    --mode=vi
    --no-history
    --error-device=stdio
    --error-device=stderr
  )

  @impl Yeesh.Command
  def name, do: "repl"

  @impl Yeesh.Command
  def description, do: "Launch an interactive Cure REPL session"

  @impl Yeesh.Command
  def usage,
    do:
      "repl [--theme=dark|light|mono] [--mode=emacs|vi]\n" <>
        "                       - interactive Cure session (:help inside)"

  @doc """
  The Yeesh help output buckets commands by `group/0` when present; we
  anchor the REPL alongside `eval` under "Cure".
  """
  @impl Yeesh.Command
  def group, do: "Cure"

  @doc """
  Offer static completions for the common option flags so the
  terminal's Tab key is useful before the REPL session starts.
  """
  @impl Yeesh.Command
  def completions(partial, _session) do
    Enum.filter(@completion_hints, &String.starts_with?(&1, partial))
  end

  @impl Yeesh.Command
  def execute(args, session) do
    {opts, warnings} = Options.parse(@default_args ++ args)

    run_repl(opts, warnings, session)
  end

  # ---------------------------------------------------------------------------

  defp run_repl(opts, warnings, session) do
    fun = repl_callable(opts)

    case CallableRunner.run(fun) do
      {:completed, output} ->
        {:ok, warnings_banner(warnings) <> output, session}

      {:interactive, io_server, task_pid, output, prompt} ->
        new_session = interactive_session(session, io_server, task_pid, prompt)
        {:ok, warnings_banner(warnings) <> output, new_session}

      {:error, reason} ->
        {:error, to_string(reason), session}
    end
  end

  # The same `:repl_start_mfa` hook honoured by `Mix.Tasks.Cure.Repl` is
  # reused here, so tests can stub the REPL launch from either entry
  # point without needing to spin up the full interactive loop.
  defp repl_callable(opts) do
    case Application.get_env(:cure, :repl_start_mfa) do
      {mod, fun, extra} when is_atom(mod) and is_atom(fun) and is_list(extra) ->
        fn -> apply(mod, fun, extra ++ [opts]) end

      _ ->
        fn -> Cure.REPL.start(opts) end
    end
  end

  defp interactive_session(session, io_server, task_pid, prompt) do
    context =
      Map.merge(session.context, %{
        mix_io_server: io_server,
        mix_task_pid: task_pid,
        mix_prompt: prompt,
        # We never touched `Mix.shell/1`, so nothing to restore. The
        # executor's `cleanup_mix_task/2` already guards on a truthy
        # original shell, so `nil` is an explicit "skip" signal.
        mix_original_shell: nil
      })

    %{session | mode: :mix_task, context: context}
  end

  defp warnings_banner([]), do: ""

  defp warnings_banner(warnings) do
    warnings
    |> Enum.map_join("\r\n", &("repl: " <> &1))
    |> Kernel.<>("\r\n")
  end
end
