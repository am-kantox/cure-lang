defmodule Cure.Story.Outline do
  @moduledoc """
  Top-down structural outline builder for `cure story` (v0.32.0).

  Walks all `.cure` source files in a project, parses them, and
  classifies AST container nodes into a hierarchical outline:

      apps -> supervisors -> actors -> fsms -> types

  The outline is a simple nested map structure consumed by
  `Cure.Story.Narrator` to generate narrative prose.
  """

  @type outline :: %{
          apps: [app_node()],
          supervisors: [sup_node()],
          actors: [actor_node()],
          fsms: [fsm_node()],
          types: [type_node()]
        }

  @type app_node :: %{name: String.t(), file: String.t(), supervisors: [String.t()], actors: [String.t()]}
  @type sup_node :: %{name: String.t(), file: String.t(), strategy: atom(), children: [String.t()]}
  @type actor_node :: %{name: String.t(), file: String.t(), effects: [String.t()], messages: [String.t()]}
  @type fsm_node :: %{name: String.t(), file: String.t(), states: [String.t()], transitions: [transition()]}
  @type type_node :: %{name: String.t(), file: String.t(), kind: :enum | :record | :alias, doc: String.t() | nil}
  @type transition :: %{from: String.t(), event: String.t(), to: String.t()}

  @doc """
  Build a structural outline from all `.cure` sources under `root`.

  Reads and parses each file silently; parse errors are skipped without
  raising.
  """
  @spec build(String.t()) :: outline()
  def build(root \\ ".") when is_binary(root) do
    files =
      root
      |> Path.join("lib/**/*.cure")
      |> Path.wildcard()
      |> Enum.sort()

    Enum.reduce(files, empty_outline(), fn file, outline ->
      case parse_file(file) do
        {:ok, ast} -> merge_outline(outline, walk(ast, file))
        {:error, _} -> outline
      end
    end)
  end

  # -- Outline accumulation -----------------------------------------------------

  defp empty_outline do
    %{apps: [], supervisors: [], actors: [], fsms: [], types: []}
  end

  defp merge_outline(acc, additions) do
    %{
      apps: acc.apps ++ additions.apps,
      supervisors: acc.supervisors ++ additions.supervisors,
      actors: acc.actors ++ additions.actors,
      fsms: acc.fsms ++ additions.fsms,
      types: acc.types ++ additions.types
    }
  end

  # -- AST walking --------------------------------------------------------------

  defp walk(ast, file) do
    walk_node(ast, file, empty_outline())
  end

  defp walk_node({:block, _, children}, file, acc) when is_list(children) do
    Enum.reduce(children, acc, fn child, a -> walk_node(child, file, a) end)
  end

  defp walk_node({:container, meta, body}, file, acc) when is_list(meta) do
    acc =
      case Keyword.get(meta, :container_type) do
        :module ->
          Enum.reduce(body, acc, fn child, a -> walk_node(child, file, a) end)

        :app ->
          node = parse_app(meta, body, file)
          %{acc | apps: [node | acc.apps]}

        :supervisor ->
          node = parse_supervisor(meta, body, file)
          %{acc | supervisors: [node | acc.supervisors]}

        :actor ->
          node = parse_actor(meta, body, file)
          %{acc | actors: [node | acc.actors]}

        :fsm ->
          node = parse_fsm(meta, body, file)
          %{acc | fsms: [node | acc.fsms]}

        :enum ->
          node = %{
            name: Keyword.get(meta, :name, "Unknown"),
            file: file,
            kind: :enum,
            doc: Keyword.get(meta, :doc)
          }

          %{acc | types: [node | acc.types]}

        :struct ->
          node = %{
            name: Keyword.get(meta, :name, "Unknown"),
            file: file,
            kind: :record,
            doc: Keyword.get(meta, :doc)
          }

          %{acc | types: [node | acc.types]}

        _ ->
          acc
      end

    acc
  end

  defp walk_node({:type_annotation, meta, _}, file, acc) when is_list(meta) do
    node = %{
      name: Keyword.get(meta, :name, "Unknown"),
      file: file,
      kind: :alias,
      doc: Keyword.get(meta, :doc)
    }

    %{acc | types: [node | acc.types]}
  end

  defp walk_node(_, _file, acc), do: acc

  # -- Container parsers --------------------------------------------------------

  defp parse_app(meta, body, file) do
    name = Keyword.get(meta, :name, "Unknown")

    supervisors =
      Enum.flat_map(body, fn
        {:root, _, [{:supervisor, _, sname}]} ->
          [sname]

        {:binding, [{:key, "root"} | _], [{:supervisor, _, sname}]} ->
          [sname]

        {:application_clause, m, _} when is_list(m) ->
          case Keyword.get(m, :clause_type) do
            :root -> [Keyword.get(m, :supervisor, "")]
            _ -> []
          end

        _ ->
          []
      end)

    actors =
      Enum.flat_map(body, fn
        {:container, m, _} when is_list(m) ->
          case Keyword.get(m, :container_type) do
            :actor -> [Keyword.get(m, :name, "")]
            _ -> []
          end

        _ ->
          []
      end)

    %{name: name, file: file, supervisors: supervisors, actors: actors}
  end

  defp parse_supervisor(meta, body, file) do
    name = Keyword.get(meta, :name, "Unknown")
    strategy = extract_strategy(body)
    children = extract_children(body)
    %{name: name, file: file, strategy: strategy, children: children}
  end

  defp parse_actor(meta, body, file) do
    name = Keyword.get(meta, :name, "Unknown")
    effects = extract_effects(meta)
    messages = extract_message_types(body)
    %{name: name, file: file, effects: effects, messages: messages}
  end

  defp parse_fsm(meta, body, file) do
    name = Keyword.get(meta, :name, "Unknown")
    transitions = extract_transitions(body)
    states = extract_states(transitions)
    %{name: name, file: file, states: states, transitions: transitions}
  end

  # -- Helper extractors --------------------------------------------------------

  defp extract_strategy(body) do
    Enum.find_value(body, :one_for_one, fn
      {:binding, [{:key, "strategy"} | _], [{:atom, _, strategy}]} -> strategy
      {:field, [{:name, "strategy"} | _], [{:atom, _, strategy}]} -> strategy
      {:assign, _, {:atom, _, strategy}} -> strategy
      _ -> nil
    end)
  end

  defp extract_children(body) do
    Enum.flat_map(body, fn
      {:children, _, children} ->
        Enum.flat_map(children, fn
          {:child, m, _} when is_list(m) -> [Keyword.get(m, :module, "?")]
          {:variable, _, name} -> [name]
          _ -> []
        end)

      _ ->
        []
    end)
  end

  defp extract_effects(meta) do
    case Keyword.get(meta, :effects) do
      nil -> []
      effects when is_list(effects) -> Enum.map(effects, &to_string/1)
    end
  end

  defp extract_message_types(body) do
    Enum.flat_map(body, fn
      {:container, m, _clauses} when is_list(m) ->
        case Keyword.get(m, :container_type) do
          :inbox ->
            Keyword.get(m, :variants, [])
            |> Enum.map(fn
              {:variant, vm, _} when is_list(vm) -> Keyword.get(vm, :name, "?")
              {:variable, _, name} -> name
              other -> inspect(other)
            end)

          _ ->
            []
        end

      _ ->
        []
    end)
  end

  defp extract_transitions(body) do
    Enum.flat_map(body, fn
      {:transition, meta, _} when is_list(meta) ->
        from = Keyword.get(meta, :from, "?")
        event = Keyword.get(meta, :event, "?")
        to = Keyword.get(meta, :to, "?")
        [%{from: to_string(from), event: to_string(event), to: to_string(to)}]

      {:fsm_rule, meta, _} when is_list(meta) ->
        from = Keyword.get(meta, :from, "?")
        event = Keyword.get(meta, :event, "?")
        to = Keyword.get(meta, :to, "?")
        [%{from: to_string(from), event: to_string(event), to: to_string(to)}]

      _ ->
        []
    end)
  end

  defp extract_states(transitions) do
    transitions
    |> Enum.flat_map(fn %{from: f, to: t} -> [f, t] end)
    |> Enum.uniq()
    |> Enum.reject(&(&1 == "?"))
    |> Enum.sort()
  end

  # -- File parsing -------------------------------------------------------------

  defp parse_file(path) do
    with {:ok, source} <- File.read(path),
         {:ok, tokens} <-
           Cure.Compiler.Lexer.tokenize(source, file: path, emit_events: false),
         {:ok, ast} <-
           Cure.Compiler.Parser.parse(tokens, file: path, emit_events: false) do
      {:ok, ast}
    else
      {:error, reason} -> {:error, reason}
    end
  end
end
