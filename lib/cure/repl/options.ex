defmodule Cure.REPL.Options do
  @moduledoc """
  Argument parsing for the Cure REPL.

  Shared between `Mix.Tasks.Cure.Repl` (the CLI entry point, used in
  development and tests) and `CureSiteWeb.Commands.CureRepl` (the
  in-browser Yeesh command, which must work inside a `MIX_ENV=prod`
  release where the `:mix` application is intentionally absent).

  The module is deliberately Mix-free: `translate/1` returns plain
  tagged tuples (`{:ok, entries}` or `{:warn, message}`) so each
  caller can decide how to surface invalid values. The Mix task pipes
  warnings through `Mix.shell().error/1`; the Yeesh command prepends
  them to the REPL banner.
  """

  @switches [
    raw: :boolean,
    theme: :string,
    mode: :string,
    history: :string,
    no_history: :boolean,
    error_device: :string
  ]

  @typedoc "Keyword list accepted by `Cure.REPL.start/1`."
  @type repl_opts :: keyword()

  @typedoc "Human-readable warning for an invalid switch value."
  @type warning :: String.t()

  @doc """
  Returns the `OptionParser` switch definition understood by the Cure
  REPL. Exposed so both entry points stay in sync.
  """
  @spec switches() :: keyword()
  def switches, do: @switches

  @doc """
  Parses a raw CLI-style argument list into REPL options.

  Returns `{opts, warnings}` where `opts` is a keyword list suitable
  for `Cure.REPL.start/1` and `warnings` is a list of messages for
  switch values that could not be mapped (e.g. `--theme=neon`).
  Unknown values are dropped rather than aborting, so callers keep
  full control of the error surface.
  """
  @spec parse([String.t()]) :: {repl_opts(), [warning()]}
  def parse(args) when is_list(args) do
    {parsed, _rest, _invalid} = OptionParser.parse(args, switches: @switches)
    build_opts(parsed)
  end

  @doc """
  Translates an already-parsed keyword list into REPL options.

  Accepts the output shape of `OptionParser.parse/2` and returns
  `{opts, warnings}`. Later occurrences of the same option win,
  preserving the historical behaviour of
  `Mix.Tasks.Cure.Repl.build_opts/1`.
  """
  @spec build_opts(keyword()) :: {repl_opts(), [warning()]}
  def build_opts(parsed) when is_list(parsed) do
    {entries, warnings} =
      Enum.reduce(parsed, {[], []}, fn pair, {entries, warnings} ->
        case translate(pair) do
          {:ok, new_entries} -> {entries ++ new_entries, warnings}
          {:warn, message} -> {entries, warnings ++ [message]}
        end
      end)

    opts =
      entries
      |> Enum.reverse()
      |> Enum.uniq_by(&elem(&1, 0))
      |> Enum.reverse()

    {opts, warnings}
  end

  # -- Translation table -----------------------------------------------------

  @spec translate({atom(), term()}) ::
          {:ok, [{atom(), term()}]} | {:warn, warning()}
  defp translate({:raw, bool}) when is_boolean(bool), do: {:ok, [{:raw, bool}]}

  defp translate({:theme, "auto"}), do: {:ok, [{:theme, :auto}]}

  defp translate({:theme, name}) when name in ~w(dark light mono),
    do: {:ok, [{:theme, String.to_atom(name)}]}

  defp translate({:theme, other}),
    do: {:warn, "unknown --theme #{inspect(other)} (expected dark|light|mono|auto)"}

  defp translate({:mode, "emacs"}), do: {:ok, [{:mode, :emacs}]}
  defp translate({:mode, "vi"}), do: {:ok, [{:mode, :vi}]}

  defp translate({:mode, other}),
    do: {:warn, "unknown --mode #{inspect(other)} (expected emacs|vi)"}

  defp translate({:history, ""}), do: {:ok, [{:history_path, nil}]}
  defp translate({:history, path}) when is_binary(path), do: {:ok, [{:history_path, path}]}

  defp translate({:no_history, true}), do: {:ok, [{:history_path, nil}]}
  defp translate({:no_history, false}), do: {:ok, []}

  defp translate({:error_device, "stdio"}), do: {:ok, [{:error_device, :stdio}]}
  defp translate({:error_device, "stderr"}), do: {:ok, [{:error_device, :stderr}]}
  defp translate({:error_device, "standard_io"}), do: {:ok, [{:error_device, :stdio}]}
  defp translate({:error_device, "standard_error"}), do: {:ok, [{:error_device, :stderr}]}

  defp translate({:error_device, other}),
    do: {:warn, "unknown --error-device #{inspect(other)} (expected stdio|stderr)"}

  defp translate(_), do: {:ok, []}
end
