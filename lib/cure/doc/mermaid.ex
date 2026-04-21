defmodule Cure.Doc.Mermaid do
  @moduledoc """
  Mermaid diagram emission for `cure doc` (v0.27.0).

  Given a MetaAST container node -- an FSM, a supervisor, or an
  application -- return a Mermaid source string. The shapes are:

    * FSM (`container_type: :fsm`)         -> `stateDiagram-v2`
    * Supervisor (`container_type: :sup`)  -> `graph TD`
    * Application (`container_type: :app`) -> `graph LR`

  ## FSM rendering

  States are extracted from the container's transitions; edges carry
  the triggering event, with `!` / `?` suffix preserved. A dedicated
  `[*] --> <initial>` edge marks the initial state; `@terminal`
  states collapse into a `<name> --> [*]` edge.

  ## Supervisor rendering

  Children are rendered as rectangular nodes labelled with the
  child-id and module, linked from the supervisor's name. The
  strategy is captured as a sub-graph caption.

  ## Application rendering

  The outer container is labelled with the application name, `vsn`,
  and root supervisor. Applications that declare `on_start` /
  `on_stop` / `on_phase` clauses are annotated alongside the root
  edge.

  ## Pipeline event

  Every successful rendering emits a `:doc_mermaid` event with
  `:emitted` and attributes `%{kind: :fsm|:sup|:app, name: String}`.
  Missing-shape containers emit nothing and return `nil`.
  """

  alias Cure.Pipeline.Events

  @doc """
  Render a single container node as Mermaid. Returns a source string
  or `nil` if the node is not an FSM / sup / app container.
  """
  @spec render(tuple(), keyword()) :: String.t() | nil
  def render(ast, opts \\ [])

  def render({:container, meta, body}, opts) when is_list(meta) do
    kind = Keyword.get(meta, :container_type)
    name = Keyword.get(meta, :name, "Unknown")
    file = Keyword.get(opts, :file, "nofile")
    line = Keyword.get(meta, :line, 1)

    src =
      case kind do
        :fsm -> render_fsm(name, meta, body)
        :sup -> render_sup(name, meta, body)
        :app -> render_app(name, meta, body)
        _ -> nil
      end

    if src do
      Events.emit(
        :doc_mermaid,
        :emitted,
        %{kind: kind, name: name},
        Events.meta(file, line)
      )
    end

    src
  end

  def render(_other, _opts), do: nil

  # -- FSM --------------------------------------------------------------------

  defp render_fsm(_name, meta, body) do
    transitions = extract_transitions(body)
    terminal = Keyword.get(meta, :terminal_states, [])

    states =
      (Enum.map(transitions, & &1.from) ++ Enum.map(transitions, & &1.to))
      |> Enum.reject(&(&1 in ["*", nil, ""]))
      |> Enum.uniq()

    initial =
      case Enum.find(transitions, &(&1.from not in ["*", nil, ""])) do
        %{from: s} -> s
        _ -> List.first(states)
      end

    header = "stateDiagram-v2"
    init_edge = if initial, do: ["  [*] --> #{state_id(initial)}"], else: []

    state_lines =
      Enum.map(states, fn s ->
        "  " <> state_id(s)
      end)

    edge_lines =
      transitions
      |> Enum.map(fn %{from: from, event: event, to: to, event_kind: kind} ->
        from_id =
          if from in ["*", nil, ""] do
            "[*]"
          else
            state_id(from)
          end

        suffix =
          case kind do
            :hard -> "!"
            :soft -> "?"
            _ -> ""
          end

        label = "#{event}#{suffix}" |> String.replace("\"", "'")
        "  #{from_id} --> #{state_id(to)} : #{label}"
      end)

    terminal_lines =
      terminal
      |> List.wrap()
      |> Enum.map(fn s -> "  #{state_id(s)} --> [*]" end)

    [header | init_edge ++ state_lines ++ edge_lines ++ terminal_lines]
    |> Enum.join("\n")
  end

  defp extract_transitions(body) do
    Enum.flat_map(body, fn
      {:function_call, fmeta, _} ->
        if Keyword.get(fmeta, :name) == "transition" do
          [
            %{
              from: Keyword.get(fmeta, :from, "*"),
              event: Keyword.get(fmeta, :event, ""),
              to: Keyword.get(fmeta, :to, ""),
              event_kind: Keyword.get(fmeta, :event_kind, :normal)
            }
          ]
        else
          []
        end

      _ ->
        []
    end)
  end

  defp state_id(s), do: String.replace(to_string(s), ~r/[^A-Za-z0-9_]/, "_")

  # -- Supervisor -------------------------------------------------------------

  defp render_sup(name, meta, body) do
    strategy = Keyword.get(meta, :strategy, :one_for_one)

    children =
      body
      |> Enum.flat_map(fn
        {:sup_child, cmeta, _} -> [cmeta]
        _ -> []
      end)

    header = "graph TD"

    sup_node = "  #{state_id(name)}((\"#{name}\\nstrategy: #{strategy}\"))"

    child_lines =
      Enum.flat_map(children, fn cmeta ->
        id = Keyword.get(cmeta, :id, "child")
        module = Keyword.get(cmeta, :module, id)
        restart = Keyword.get(cmeta, :restart, :permanent)

        node_label = "#{id}\\n#{module}\\n#{restart}"

        [
          "  #{state_id(id)}[\"#{node_label}\"]",
          "  #{state_id(name)} --> #{state_id(id)}"
        ]
      end)

    [header, sup_node | child_lines]
    |> Enum.join("\n")
  end

  # -- Application ------------------------------------------------------------

  defp render_app(name, meta, _body) do
    vsn = Keyword.get(meta, :vsn, "0.0.0")
    root = Keyword.get(meta, :root, "—")
    applications = Keyword.get(meta, :applications, [])

    header = "graph LR"

    app_node = "  #{state_id(name)}((\"app #{name}\\nvsn #{vsn}\"))"

    root_edges =
      cond do
        root in [nil, "—", ""] ->
          []

        true ->
          [
            "  #{state_id(name)} --> #{state_id(to_string(root))}[\"root: #{root}\"]"
          ]
      end

    applications_edges =
      applications
      |> Enum.map(fn dep ->
        "  #{state_id(name)} -.-> #{state_id(to_string(dep))}([\"#{dep}\"])"
      end)

    [header, app_node | root_edges ++ applications_edges]
    |> Enum.join("\n")
  end
end
