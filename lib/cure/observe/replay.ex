defmodule Cure.Observe.Replay do
  @moduledoc """
  Replays a `Cure.Observe.Journal` trace against a fresh FSM process.

  ## Usage

      {:ok, entries} = Cure.Observe.Journal.load(".cure-trace/abc123.journal")
      Cure.Observe.Replay.replay(MyFsmModule, entries, step: :auto)

  ## Replay modes

  - `:auto` -- replay all events without pausing (default)
  - `:step` -- pause after each event and wait for user input

  ## Event rendering

  Each replayed event is printed to stdout with its before/after state
  in a compact diff format:

      [  1] locked     --coin-->    unlocked   (ok)
      [  2] unlocked   --push-->    locked     (ok)

  """

  @doc """
  Replay a list of journal entries against a freshly started FSM module.

  ## Options

    * `:step` -- boolean, if true pauses after each event for [Enter]
    * `:print` -- boolean, if false suppresses output (default: true)
    * `:on_event` -- `(n, from, event, to, result -> any)` callback

  Returns `{:ok, results}` where `results` is a list of
  `{state_before, event, state_after, :ok | {:error, term()}}`.
  """
  @spec replay(module(), list(), keyword()) :: {:ok, list()} | {:error, term()}
  def replay(fsm_module, entries, opts \\ []) do
    step? = Keyword.get(opts, :step, false)
    print? = Keyword.get(opts, :print, true)
    on_event = Keyword.get(opts, :on_event)

    case start_fsm(fsm_module) do
      {:ok, pid} ->
        results =
          entries
          |> Enum.with_index(1)
          |> Enum.map(fn {{_actor_id, from, event, to, _ts}, n} ->
            _ = send_event(pid, event)
            {actual_from, _payload} = fsm_state(pid)

            outcome =
              cond do
                actual_from == to -> :ok
                actual_from == from -> {:error, :state_unchanged}
                true -> {:error, {:unexpected_state, actual_from}}
              end

            if print? do
              print_step(n, from, event, to, outcome)
            end

            if is_function(on_event, 5) do
              on_event.(n, from, event, to, outcome)
            end

            if step? do
              IO.write("  [Enter to continue, q to quit] ")

              case IO.gets("") do
                "q\n" -> throw(:quit)
                _ -> :ok
              end
            end

            {from, event, to, outcome}
          end)

        GenServer.stop(pid, :normal)
        {:ok, results}

      {:error, _} = err ->
        err
    end
  catch
    :quit -> {:ok, :quit}
  end

  @doc """
  Pretty-print a list of journal entries without replaying them.
  """
  @spec print_trace(list()) :: :ok
  def print_trace(entries) do
    entries
    |> Enum.with_index(1)
    |> Enum.each(fn {{_id, from, event, to, ts}, n} ->
      print_step(n, from, event, to, :ok)
      IO.puts("        ts=#{ts}")
    end)

    :ok
  end

  # -- Helpers -----------------------------------------------------------------

  defp start_fsm(module) do
    try do
      case module.start_link() do
        {:ok, pid} -> {:ok, pid}
        {:error, _} = err -> err
        other -> {:error, {:unexpected_start, other}}
      end
    rescue
      e -> {:error, {:start_failed, Exception.message(e)}}
    end
  end

  defp send_event(pid, event) do
    try do
      GenServer.cast(pid, {:event, event, nil})
      :timer.sleep(10)
      :ok
    rescue
      e -> {:error, Exception.message(e)}
    end
  end

  defp fsm_state(pid) do
    try do
      GenServer.call(pid, :get_state, 1000)
    rescue
      _ -> {:unknown, nil}
    end
  end

  defp print_step(n, from, event, to, outcome) do
    n_str = String.pad_leading(Integer.to_string(n), 3)
    from_str = String.pad_trailing(Atom.to_string(from), 14)
    to_str = String.pad_trailing(Atom.to_string(to), 14)
    ev_str = String.pad_trailing(Atom.to_string(event), 12)

    status =
      case outcome do
        :ok -> "ok"
        {:error, :state_unchanged} -> "WARN: state unchanged"
        {:error, {:unexpected_state, got}} -> "WARN: got #{got}"
        _ -> "?"
      end

    IO.puts("[#{n_str}] #{from_str} --#{ev_str}--> #{to_str} (#{status})")
  end
end
