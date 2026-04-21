defmodule Mix.Tasks.Cure.Trace do
  @moduledoc """
  Attach a typed tracer to `Module.function/arity`.

  ## Usage

      mix cure.trace Cure.Std.List.map/2
      mix cure.trace Cure.Std.Io.println/1 --duration 5

  The task starts a tracer, sleeps for `--duration` seconds
  (default 10), then stops tracing and exits. Use another shell
  (or Livebook) to exercise the traced code during the window.
  """

  use Mix.Task

  @shortdoc "Trace Module.fun/arity with Cure.Observe.Trace"

  @impl Mix.Task
  def run(args) do
    Application.ensure_all_started(:cure)

    {opts, positional, _} =
      OptionParser.parse(args, switches: [duration: :integer])

    mfa =
      case positional do
        [target | _] -> parse_mfa(target)
        _ -> raise "pass Module.fun/arity, e.g. Cure.Std.List.map/2"
      end

    duration = Keyword.get(opts, :duration, 10) * 1000

    Mix.shell().info("Tracing #{inspect(elem(mfa, 0))}.#{elem(mfa, 1)}/#{elem(mfa, 2)} for #{div(duration, 1000)}s...")

    Cure.Observe.Trace.start(mfa)
    :timer.sleep(duration)
    Cure.Observe.Trace.stop()
    Mix.shell().info("Trace stopped.")
  end

  defp parse_mfa(target) when is_binary(target) do
    case Regex.run(~r/^([\w\.]+)\.(\w+)\/(\d+)$/, target) do
      [_, mod, fun, arity] ->
        mod_atom =
          if String.starts_with?(mod, ":"),
            do: String.to_atom(String.slice(mod, 1..-1//1)),
            else: Module.concat([mod])

        {mod_atom, String.to_atom(fun), String.to_integer(arity)}

      _ ->
        raise "cannot parse #{inspect(target)}; expected Module.fun/arity"
    end
  end
end
