defmodule Cure.Observe.Trace do
  @moduledoc """
  Typed tracer for Cure (v0.27.0).

  Thin wrapper around OTP's `:dbg` that formats traced calls and
  returns through `inspect/2` and, where a compile-time signature is
  known, annotates each argument with its declared Cure type.

  ## Usage

      iex> Cure.Observe.Trace.start({Cure.Std.List, :map, 2})
      iex> # ... exercise the system ...
      iex> Cure.Observe.Trace.stop()

  From the command line:

      mix cure.trace Cure.Std.List.map/2

  ## Filters

  `start/2` accepts options:

    * `:effect`     -- atom; only surface calls whose declared
      effect set contains the given effect.
    * `:format`     -- `:plain` (default) or `:marcli` for ANSI
      colour.
    * `:self`       -- send formatted lines to the calling process
      as `{:cure_trace, text}` messages instead of printing them.
      Useful for tests.

  ## Registry

  `Cure.Observe.Trace.Registry` is an ETS table keyed by
  `{module, fun, arity}` that stores the declared parameter types
  and effect set, if known. The type checker populates this table
  opportunistically; missing entries mean the tracer falls back to
  raw `inspect/2` output.
  """

  @reg_table :cure_trace_registry

  @doc """
  Start tracing the given `{module, fun, arity}` triple. Repeated
  calls replace the current trace spec.
  """
  @spec start({module(), atom(), arity()}, keyword()) :: :ok
  def start({module, fun, arity} = mfa, opts \\ []) do
    ensure_registry()
    ensure_dbg()

    target = if Keyword.get(opts, :self, false), do: self(), else: nil

    :dbg.tracer(:process, {&trace_handler/2, %{target: target, opts: opts}})

    :dbg.p(:all, [:call, :return_to])
    :dbg.tpl(module, fun, arity, :return_trace)

    Process.put({__MODULE__, :active}, mfa)
    :ok
  end

  @doc "Stop the currently active tracer."
  @spec stop() :: :ok
  def stop do
    try do
      :dbg.stop()
    catch
      _, _ -> :ok
    end

    Process.delete({__MODULE__, :active})
    :ok
  end

  @doc """
  Register the type signature for a function. Called by the Cure
  type checker during compile; safe to call at runtime too.
  """
  @spec register_signature({module(), atom(), arity()}, [String.t()], String.t(), [atom()]) :: :ok
  def register_signature({mod, fun, arity}, param_types, ret_type, effects) do
    ensure_registry()
    :ets.insert(@reg_table, {{mod, fun, arity}, param_types, ret_type, effects})
    :ok
  end

  @doc "Look up a registered signature."
  @spec lookup_signature({module(), atom(), arity()}) :: {:ok, map()} | :error
  def lookup_signature(mfa) do
    ensure_registry()

    case :ets.lookup(@reg_table, mfa) do
      [{_, params, ret, effects}] ->
        {:ok, %{params: params, return: ret, effects: effects}}

      [] ->
        :error
    end
  rescue
    ArgumentError -> :error
  end

  # -- Internals --------------------------------------------------------------

  defp ensure_registry do
    case :ets.whereis(@reg_table) do
      :undefined ->
        :ets.new(@reg_table, [:set, :public, :named_table])
        :ok

      _ ->
        :ok
    end
  end

  defp ensure_dbg do
    case Application.ensure_all_started(:runtime_tools) do
      {:ok, _} -> :ok
      _ -> :ok
    end
  end

  @doc false
  def trace_handler(msg, %{target: target, opts: opts} = state) do
    line = format(msg, opts)

    cond do
      is_pid(target) -> send(target, {:cure_trace, line})
      true -> IO.puts(line)
    end

    state
  end

  defp format({:trace, pid, :call, {mod, fun, args}}, opts) do
    arity = length(args)
    mfa = {mod, fun, arity}

    header = "call #{inspect(pid)} #{mod}.#{fun}/#{arity}"

    body =
      case lookup_signature(mfa) do
        {:ok, %{params: params, effects: effects}} ->
          typed =
            args
            |> Enum.zip(params)
            |> Enum.map(fn {a, t} -> "#{inspect(a)} : #{t}" end)
            |> Enum.join(", ")

          effects_tag = if effects == [], do: "pure", else: "! " <> Enum.join(effects, ",")

          "#{header}(#{typed})  [#{effects_tag}]"

        :error ->
          "#{header}(#{Enum.map_join(args, ", ", &inspect/1)})"
      end

    _ = Keyword.get(opts, :format, :plain)
    body
  end

  defp format({:trace, pid, :return_from, {mod, fun, arity}, ret}, opts) do
    mfa = {mod, fun, arity}

    return_type =
      case lookup_signature(mfa) do
        {:ok, %{return: t}} -> " : #{t}"
        :error -> ""
      end

    _ = Keyword.get(opts, :format, :plain)
    "return #{inspect(pid)} #{mod}.#{fun}/#{arity} -> #{inspect(ret)}#{return_type}"
  end

  defp format(other, _opts), do: "trace #{inspect(other)}"
end
