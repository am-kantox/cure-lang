defmodule Cure.SMT.Process do
  @moduledoc """
  Manages a Z3 SMT solver process via an Erlang port.

  Starts Z3 in interactive SMT-LIB2 mode (`z3 -smt2 -in`) and provides
  query execution with timeout handling.

  ## Usage

      {:ok, pid} = Cure.SMT.Process.start_link()
      {:sat, _} = Cure.SMT.Process.query(pid, "(check-sat)")
      :ok = Cure.SMT.Process.stop(pid)
  """

  use GenServer

  defstruct [:port, :timeout, buffer: "", query_count: 0]

  @default_timeout 5_000

  # -- Public API --------------------------------------------------------------

  @doc "Start a Z3 solver process."
  @spec start_link(keyword()) :: GenServer.on_start()
  def start_link(opts \\ []) do
    timeout = Keyword.get(opts, :timeout, @default_timeout)
    GenServer.start_link(__MODULE__, %{timeout: timeout})
  end

  @doc """
  Execute an SMT-LIB2 query string and return the result.

  Returns `{:sat, output}`, `{:unsat, output}`, `{:unknown, output}`,
  or `{:error, reason}`.
  """
  @spec query(GenServer.server(), iodata()) ::
          {:sat, String.t()} | {:unsat, String.t()} | {:unknown, String.t()} | {:error, term()}
  def query(pid, smt_query) do
    GenServer.call(pid, {:query, IO.iodata_to_binary(smt_query)}, 10_000)
  end

  @doc "Stop the solver process."
  @spec stop(GenServer.server()) :: :ok
  def stop(pid), do: GenServer.stop(pid)

  @doc "Check if Z3 is available on the system."
  @spec z3_available?() :: boolean()
  def z3_available? do
    case System.find_executable("z3") do
      nil -> false
      _ -> true
    end
  end

  # -- GenServer Callbacks -----------------------------------------------------

  @impl true
  def init(%{timeout: timeout}) do
    case find_and_open_z3() do
      {:ok, port} ->
        {:ok, %__MODULE__{port: port, timeout: timeout}}

      {:error, reason} ->
        {:stop, reason}
    end
  end

  @impl true
  def handle_call({:query, smt_query}, _from, state) do
    port = state.port

    # Send the query followed by a sentinel echo so we know when output ends
    # Z3 in -in mode processes commands sequentially; we append (echo "<<END>>")
    # to detect the end of output.
    sentinel = "<<CURE_END>>"
    full_query = smt_query <> "\n(echo \"#{sentinel}\")\n"

    Port.command(port, full_query)

    # Collect output until we see the sentinel
    result = collect_response(port, sentinel, state.timeout, [])
    state = %{state | query_count: state.query_count + 1}

    case result do
      {:ok, output} ->
        classification = classify_output(output)
        {:reply, classification, state}

      {:error, reason} ->
        {:reply, {:error, reason}, state}
    end
  end

  @impl true
  def handle_info({_port, {:data, _data}}, state) do
    # Stray port data outside of a query -- ignore
    {:noreply, state}
  end

  @impl true
  def terminate(_reason, %{port: port}) when is_port(port) do
    try do
      Port.close(port)
    catch
      _, _ -> :ok
    end

    :ok
  end

  def terminate(_reason, _state), do: :ok

  # -- Internal ----------------------------------------------------------------

  defp find_and_open_z3 do
    case System.find_executable("z3") do
      nil ->
        {:error, :z3_not_found}

      z3_path ->
        try do
          port =
            Port.open({:spawn_executable, z3_path}, [
              :binary,
              :exit_status,
              :use_stdio,
              :hide,
              args: ["-smt2", "-in"],
              line: 16_384
            ])

          {:ok, port}
        rescue
          e -> {:error, {:port_open_failed, e}}
        end
    end
  end

  defp collect_response(port, sentinel, timeout, acc) do
    receive do
      {^port, {:data, {:eol, line}}} ->
        if String.contains?(line, sentinel) do
          # Done -- join accumulated lines
          output = acc |> Enum.reverse() |> Enum.join("\n") |> String.trim()
          {:ok, output}
        else
          collect_response(port, sentinel, timeout, [line | acc])
        end

      {^port, {:data, {:noeol, chunk}}} ->
        collect_response(port, sentinel, timeout, [chunk | acc])

      {^port, {:exit_status, code}} ->
        {:error, {:solver_exited, code}}
    after
      timeout ->
        {:error, :timeout}
    end
  end

  defp classify_output(output) do
    cond do
      String.starts_with?(output, "unsat") -> {:unsat, output}
      String.starts_with?(output, "sat") -> {:sat, output}
      String.starts_with?(output, "unknown") -> {:unknown, output}
      String.contains?(output, "error") -> {:error, {:solver_error, output}}
      true -> {:unknown, output}
    end
  end
end
