defmodule Cure.Doc.Ascii do
  @moduledoc """
  ASCII / Unicode box-drawing diagrams for FSM, supervisor, and
  application containers. Complements the v0.27.0 Mermaid emitter for
  terminals that cannot render Mermaid (the `cure top` panel, plain
  shells, CI logs).

  ## Public API

  * `render/2` -- accepts a `{:container, meta, body}` AST node and
    returns the diagram source. Returns `nil` for non-FSM/sup/app
    containers.
  * `render_file/2` -- parses a `.cure` source file and renders every
    diagrammable container as one document, joined by blank lines.

  ## Renderings

  * **FSM** -- one box per state, with arrows labelled by event name
    and `!`/`?` suffix preserved. The initial state gets a leading
    `*-->` marker; `@terminal` states get a trailing `-->*`.
  * **Supervisor** -- vertical tree using `├──` and `└──` glyphs;
    children carry id, module, and restart policy. The strategy
    appears under the supervisor's name as `(strategy: one_for_one)`.
  * **Application** -- one panel summarising the app, its root
    supervisor, vsn, and declared applications. The body of the
    panel reuses the supervisor renderer when the app's `root` is a
    statically resolvable supervisor name.

  The renderings are deliberately simple: one diagram per AST node,
  no horizontal layouts, no column alignment, no graph algorithms.
  v0.31.0 ships them as a static counterpart to the v0.27.0 Mermaid
  surface; richer layouts (kitty graphics, sized canvases) can come
  later.

  ## Pipeline event

  Every successful render emits a `:doc_ascii` pipeline event under
  the `:doc_mermaid` stage so existing observability hooks see both
  emitter kinds without further plumbing.
  """

  alias Cure.Pipeline.Events

  @doc "Render a single container AST node as ASCII. Returns `nil` if not a diagram container."
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
        :doc_ascii,
        %{kind: kind, name: name},
        Events.meta(file, line)
      )
    end

    src
  end

  def render(_other, _opts), do: nil

  @doc """
  Parse `path` as a Cure source file and render every diagrammable
  container in source order. Returns `{:ok, source}` or
  `{:error, reason}`.

  ## Options

  * `:filter` -- one of `:fsm`, `:sup`, `:app`, or `:all` (default).
    Render only containers of the specified kind.
  """
  @spec render_file(Path.t(), keyword()) :: {:ok, String.t()} | {:error, term()}
  def render_file(path, opts \\ []) do
    filter = Keyword.get(opts, :filter, :all)

    with {:ok, source} <- File.read(path),
         {:ok, tokens} <- Cure.Compiler.Lexer.tokenize(source, file: path, emit_events: false),
         {:ok, ast} <- Cure.Compiler.Parser.parse(tokens, file: path, emit_events: false) do
      diagrams =
        ast
        |> collect_containers()
        |> Enum.filter(&filter_kind?(&1, filter))
        |> Enum.map(&render(&1, file: path))
        |> Enum.reject(&is_nil/1)

      case diagrams do
        [] -> {:ok, ""}
        list -> {:ok, Enum.join(list, "\n\n")}
      end
    end
  end

  defp collect_containers({:container, meta, _body} = c) when is_list(meta) do
    [c]
  end

  defp collect_containers({:block, _meta, children}) when is_list(children) do
    Enum.flat_map(children, &collect_containers/1)
  end

  defp collect_containers(_), do: []

  defp filter_kind?(_node, :all), do: true

  defp filter_kind?({:container, meta, _}, kind) do
    Keyword.get(meta, :container_type) == kind
  end

  # ============================================================================
  # FSM
  # ============================================================================

  defp render_fsm(name, meta, body) do
    transitions = extract_transitions(body)
    terminal = Keyword.get(meta, :terminal_states, []) |> List.wrap()

    states =
      (Enum.map(transitions, & &1.from) ++ Enum.map(transitions, & &1.to))
      |> Enum.reject(&(&1 in ["*", nil, ""]))
      |> Enum.uniq()

    initial =
      case Enum.find(transitions, &(&1.from not in ["*", nil, ""])) do
        %{from: s} -> s
        _ -> List.first(states)
      end

    header = ["fsm #{name}", String.duplicate("=", String.length("fsm " <> to_string(name)))]

    init_line = if initial, do: ["", "  *──> #{initial}"], else: []

    state_section =
      states
      |> Enum.map(fn s ->
        marker = if s in terminal, do: "▣", else: "▢"
        "  #{marker} #{s}"
      end)

    edge_section =
      Enum.map(transitions, fn t ->
        from_id = if t.from in ["*", nil, ""], do: "*", else: t.from
        suffix = event_suffix(t.event_kind)
        "  #{from_id} ──[#{t.event}#{suffix}]──> #{t.to}"
      end)

    terminal_lines =
      Enum.map(terminal, fn s -> "  #{s} ──> *" end)

    sections =
      [header, init_line, ["", "states:" | state_section], ["", "transitions:" | edge_section]]

    sections =
      if terminal_lines == [] do
        sections
      else
        sections ++ [["", "terminal:" | terminal_lines]]
      end

    sections
    |> Enum.map(&Enum.join(&1, "\n"))
    |> Enum.join("\n")
  end

  defp event_suffix(:hard), do: "!"
  defp event_suffix(:soft), do: "?"
  defp event_suffix(_), do: ""

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

  # ============================================================================
  # Supervisor
  # ============================================================================

  defp render_sup(name, meta, body) do
    strategy = Keyword.get(meta, :strategy, :one_for_one)

    children =
      body
      |> Enum.flat_map(fn
        {:sup_child, cmeta, _} -> [cmeta]
        _ -> []
      end)

    header = "sup #{name} (strategy: #{strategy})"
    underline = String.duplicate("=", String.length(header))

    child_lines =
      children
      |> Enum.with_index()
      |> Enum.map(fn {cmeta, idx} ->
        last? = idx == length(children) - 1
        glyph = if last?, do: "└──", else: "├──"
        id = Keyword.get(cmeta, :id, "child")
        module = Keyword.get(cmeta, :module, id)
        restart = Keyword.get(cmeta, :restart, :permanent)
        "  #{glyph} #{id} :: #{module} (#{restart})"
      end)

    [header, underline, "" | child_lines]
    |> Enum.join("\n")
  end

  # ============================================================================
  # Application
  # ============================================================================

  defp render_app(name, meta, _body) do
    vsn = Keyword.get(meta, :vsn, "0.0.0")
    root = Keyword.get(meta, :root, "—")
    applications = Keyword.get(meta, :applications, [])

    description = Keyword.get(meta, :description, "")

    header = "app #{name} (vsn #{vsn})"
    underline = String.duplicate("=", String.length(header))

    desc_line =
      if is_binary(description) and description != "" do
        ["", "description: #{description}"]
      else
        []
      end

    root_lines =
      cond do
        root in [nil, "—", ""] -> []
        true -> ["", "root: #{root}"]
      end

    applications_lines =
      case applications do
        [] ->
          []

        deps ->
          ["", "applications:" | Enum.map(deps, fn d -> "  ├── #{d}" end)]
      end

    [[header, underline], desc_line, root_lines, applications_lines]
    |> List.flatten()
    |> Enum.join("\n")
  end
end
