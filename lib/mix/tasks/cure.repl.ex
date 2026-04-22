defmodule Mix.Tasks.Cure.Repl do
  @moduledoc """
  Launches the interactive Cure REPL from inside a Mix project.

  Functionally identical to `./cure repl`, but usable from any Elixir
  project that has `:cure` on its dependency path. The task starts the
  `:cure` application, parses a small set of options, and delegates to
  `Cure.REPL.start/1`.

  ## Usage

      mix cure.repl
      mix cure.repl --theme=light
      mix cure.repl --no-raw --error-device=stdio
      mix cure.repl --history=/tmp/cure.history
      mix cure.repl --no-history

  ## Options

    * `--raw` / `--no-raw` -- force raw-mode line editing on or off.
      Default is `:auto`: the REPL detects whether it is attached to a
      controlling tty. Embedders that route I/O through a custom group
      leader (for example `Yeesh.IOServer`) should pass `--no-raw` so
      the line-mode fallback kicks in.
    * `--theme` -- one of `dark`, `light`, `mono`, `auto`. Default `auto`.
    * `--mode` -- initial editing mode: `emacs` or `vi`. Default `emacs`.
    * `--history` -- path to the history file. Default `~/.cure_history`.
    * `--no-history` -- disable history persistence.
    * `--error-device` -- where compiler diagnostics go: `stderr`
      (default) or `stdio`. Embedders that rely on the task's group
      leader should pass `--error-device=stdio`.

  ## Examples

      # Standalone, full raw-mode experience.
      mix cure.repl

      # Hosted under a custom group leader (no tty, plain line mode,
      # errors routed to stdio for the embedder to capture).
      mix cure.repl --no-raw --error-device=stdio --no-history
  """

  use Mix.Task

  @shortdoc "Starts the interactive Cure REPL"

  @switches [
    raw: :boolean,
    theme: :string,
    mode: :string,
    history: :string,
    no_history: :boolean,
    error_device: :string
  ]

  @impl Mix.Task
  def run(args) do
    Mix.Task.run("app.start", [])

    {parsed, _rest, _invalid} = OptionParser.parse(args, switches: @switches)

    parsed
    |> build_opts()
    |> start_repl()
  end

  @doc false
  @spec build_opts(keyword()) :: keyword()
  def build_opts(parsed) do
    parsed
    |> Enum.flat_map(&translate/1)
    |> Enum.reverse()
    |> Enum.uniq_by(&elem(&1, 0))
    |> Enum.reverse()
  end

  # Dispatch kept private so the task is mockable in tests: overriding
  # `start_repl/1` via an application env lets us exercise the full
  # arg-parsing path without blocking on `Cure.REPL.start/1`.
  defp start_repl(opts) do
    case Application.get_env(:cure, :repl_start_mfa) do
      {mod, fun, extra} when is_atom(mod) and is_atom(fun) and is_list(extra) ->
        apply(mod, fun, extra ++ [opts])

      _ ->
        Cure.REPL.start(opts)
    end
  end

  # -- translate each parsed switch into `Cure.REPL.start/1` keyword ---------

  defp translate({:raw, bool}) when is_boolean(bool), do: [{:raw, bool}]

  defp translate({:theme, "auto"}), do: [{:theme, :auto}]

  defp translate({:theme, name}) when name in ["dark", "light", "mono"],
    do: [{:theme, String.to_atom(name)}]

  defp translate({:theme, other}) do
    Mix.shell().error("cure.repl: unknown --theme #{inspect(other)} (expected dark|light|mono|auto)")
    []
  end

  defp translate({:mode, "emacs"}), do: [{:mode, :emacs}]
  defp translate({:mode, "vi"}), do: [{:mode, :vi}]

  defp translate({:mode, other}) do
    Mix.shell().error("cure.repl: unknown --mode #{inspect(other)} (expected emacs|vi)")
    []
  end

  defp translate({:history, ""}), do: [{:history_path, nil}]
  defp translate({:history, path}) when is_binary(path), do: [{:history_path, path}]

  defp translate({:no_history, true}), do: [{:history_path, nil}]
  defp translate({:no_history, false}), do: []

  defp translate({:error_device, "stdio"}), do: [{:error_device, :stdio}]
  defp translate({:error_device, "stderr"}), do: [{:error_device, :stderr}]
  defp translate({:error_device, "standard_io"}), do: [{:error_device, :stdio}]
  defp translate({:error_device, "standard_error"}), do: [{:error_device, :stderr}]

  defp translate({:error_device, other}) do
    Mix.shell().error("cure.repl: unknown --error-device #{inspect(other)} (expected stdio|stderr)")
    []
  end

  defp translate(_), do: []
end
