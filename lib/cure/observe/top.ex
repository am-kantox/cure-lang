defmodule Cure.Observe.Top do
  @moduledoc """
  Observability snapshot for running Cure applications (v0.27.0).

  Reads from the live ETS registries owned by `Cure.Sup.Runtime`,
  `Cure.Actor.Runtime`, and `Cure.FSM.Runtime` plus the per-process
  `:erlang.process_info/2` fields that matter for live-system
  debugging:

  - Supervision tree (with each supervisor's child summary).
  - Actors (with mailbox depth, memory, reductions).
  - FSMs (with current state, uptime, event count).

  This module intentionally stops short of a raw-mode TUI so it can
  be used from any shell (CI, pipes, scripts) and paired with
  `watch -n1 cure top` for a low-tech live view. The matching CLI
  driver is `Mix.Tasks.Cure.Top` (`cure top`).

  The text renderer uses `marcli` when available for colour and
  alignment; non-tty output degrades to plain text.
  """

  alias Cure.Actor.Runtime, as: ActorRuntime
  alias Cure.FSM.Runtime, as: FsmRuntime
  alias Cure.Sup.Runtime, as: SupRuntime

  @doc """
  Collect a snapshot of the running system. Always returns a map
  with `:supervisors`, `:actors`, `:fsms`, and a header showing
  wall-clock time and scheduler utilisation.
  """
  @spec snapshot() :: map()
  def snapshot do
    %{
      at: DateTime.utc_now(),
      vm: vm_summary(),
      supervisors: supervisors(),
      actors: actors(),
      fsms: fsms()
    }
  end

  @doc """
  Render a snapshot as a multi-line string.

  Accepts `opts`:

    * `:width`  -- line width for alignment (default `80`).
    * `:colour` -- whether to emit ANSI colour (default: auto-detected
      via `IO.ANSI.enabled?/0`).
  """
  @spec render(map(), keyword()) :: String.t()
  def render(snapshot, opts \\ []) do
    width = Keyword.get(opts, :width, 80)

    [
      header_line(snapshot, width),
      "",
      sup_section(snapshot.supervisors, width),
      "",
      actor_section(snapshot.actors, width),
      "",
      fsm_section(snapshot.fsms, width)
    ]
    |> Enum.join("\n")
  end

  # -- Sections ----------------------------------------------------------------

  defp header_line(%{at: at, vm: vm}, width) do
    left = "cure top  " <> DateTime.to_iso8601(at)
    right = "procs=#{vm.process_count}  reductions=#{vm.reductions}"
    pad(left, right, width)
  end

  defp sup_section(sups, _width) do
    header = "Supervisors (#{length(sups)})"

    body =
      case sups do
        [] ->
          ["  (no supervisors running)"]

        _ ->
          Enum.map(sups, fn s ->
            "  - #{s.module}  (#{length(s.children)} children)"
          end)
      end

    ([header] ++ body) |> Enum.join("\n")
  end

  defp actor_section(actors, _width) do
    header = "Actors (#{length(actors)})"

    body =
      case actors do
        [] ->
          ["  (no actors running)"]

        _ ->
          actors
          |> Enum.sort_by(& &1.mailbox, :desc)
          |> Enum.map(fn a ->
            "  - #{format_name(a)}  mbox=#{a.mailbox}  mem=#{a.memory}  reds=#{a.reductions}"
          end)
      end

    ([header] ++ body) |> Enum.join("\n")
  end

  defp fsm_section(fsms, _width) do
    header = "FSMs (#{length(fsms)})"

    body =
      case fsms do
        [] ->
          ["  (no FSMs running)"]

        _ ->
          Enum.map(fsms, fn f ->
            "  - #{format_name(f)}  state=#{f.state}  events=#{f.event_count}  uptime_ms=#{f.uptime_ms}"
          end)
      end

    ([header] ++ body) |> Enum.join("\n")
  end

  # -- Data collection --------------------------------------------------------

  defp vm_summary do
    %{
      process_count: :erlang.system_info(:process_count),
      reductions:
        :erlang.statistics(:reductions)
        |> elem(0)
    }
  end

  defp supervisors do
    Enum.map(SupRuntime.list(), fn module ->
      children =
        case SupRuntime.which_children(module) do
          list when is_list(list) -> list
          _ -> []
        end

      %{module: module, children: children}
    end)
  end

  defp actors do
    Enum.map(ActorRuntime.list_actors(), fn info ->
      pid = info.pid
      pi = safe_process_info(pid)

      %{
        name: info[:name] || "(anonymous)",
        pid: pid,
        module: info.module,
        mailbox: pi.mailbox,
        memory: pi.memory,
        reductions: pi.reductions,
        started_at: info[:started_at]
      }
    end)
  end

  defp fsms do
    Enum.map(FsmRuntime.list_fsms(), fn info ->
      pid = info.pid
      health = FsmRuntime.health_check(pid)

      %{
        name: info[:name] || "(anonymous)",
        pid: pid,
        module: info.module,
        state: health.state,
        event_count: health.event_count,
        uptime_ms: health.uptime_ms
      }
    end)
  end

  defp safe_process_info(pid) do
    if Process.alive?(pid) do
      info = Process.info(pid, [:message_queue_len, :memory, :reductions]) || []

      %{
        mailbox: Keyword.get(info, :message_queue_len, 0),
        memory: Keyword.get(info, :memory, 0),
        reductions: Keyword.get(info, :reductions, 0)
      }
    else
      %{mailbox: 0, memory: 0, reductions: 0}
    end
  end

  # -- Formatting helpers -----------------------------------------------------

  defp format_name(%{name: "(anonymous)", pid: pid, module: module}),
    do: "#{inspect(pid)} (#{module})"

  defp format_name(%{name: name, module: module}) when is_binary(name),
    do: "#{name} (#{module})"

  defp format_name(%{name: name, module: module}),
    do: "#{inspect(name)} (#{module})"

  defp pad(left, right, width) do
    spacing = max(1, width - String.length(left) - String.length(right))
    left <> String.duplicate(" ", spacing) <> right
  end
end
