defmodule Cure.LSP.Symbols do
  @moduledoc """
  Symbol extraction from Cure AST for LSP features.

  Builds a list of symbols (modules, functions, types, FSMs) from a parsed
  AST, suitable for `textDocument/documentSymbol` responses.
  """

  @doc """
  Extract symbols from a parsed AST.

  Returns a list of LSP DocumentSymbol maps.
  """
  @spec extract(tuple()) :: [map()]
  def extract(ast) do
    case ast do
      {:container, meta, body} -> extract_container(meta, body)
      {:block, _, children} -> Enum.flat_map(children, &extract/1)
      _ -> []
    end
  end

  defp extract_container(meta, body) do
    type = Keyword.get(meta, :container_type, :unknown)
    name = Keyword.get(meta, :name, "unnamed")
    line = Keyword.get(meta, :line, 1)

    kind =
      case type do
        :module -> 2
        :fsm -> 2
        :protocol -> 11
        :trait -> 12
        :struct -> 23
        _ -> 2
      end

    children = Enum.flat_map(body, &extract_body_item/1)

    # For FSMs, also include callback blocks and annotations as children
    fsm_children =
      if type == :fsm do
        extract_fsm_meta_children(meta, line)
      else
        []
      end

    [
      %{
        "name" => name,
        "kind" => kind,
        "range" => lsp_range(line),
        "selectionRange" => lsp_range(line),
        "detail" => fsm_detail(type, meta),
        "children" => children ++ fsm_children
      }
    ]
  end

  defp fsm_detail(:fsm, meta) do
    parts = []

    parts =
      if Keyword.has_key?(meta, :on_transition),
        do: ["callback mode" | parts],
        else: ["simple mode" | parts]

    parts = if Keyword.get(meta, :timer), do: ["timer" | parts], else: parts
    Enum.join(parts, ", ")
  end

  defp fsm_detail(type, _meta), do: to_string(type)

  defp extract_fsm_meta_children(meta, line) do
    callbacks =
      ~w(on_transition on_enter on_exit on_failure on_timer)a
      |> Enum.flat_map(fn cb_name ->
        case Keyword.get(meta, cb_name) do
          clauses when is_list(clauses) and clauses != [] ->
            [
              %{
                "name" => to_string(cb_name),
                "kind" => 12,
                "detail" => "#{length(clauses)} clause(s)",
                "range" => lsp_range(line),
                "selectionRange" => lsp_range(line)
              }
            ]

          _ ->
            []
        end
      end)

    timer_children =
      case Keyword.get(meta, :timer) do
        ms when is_integer(ms) ->
          [
            %{
              "name" => "@timer #{ms}ms",
              "kind" => 14,
              "range" => lsp_range(line),
              "selectionRange" => lsp_range(line)
            }
          ]

        _ ->
          []
      end

    callbacks ++ timer_children
  end

  defp extract_body_item({:function_def, meta, _body}) do
    name = Keyword.get(meta, :name, "unknown")
    arity = Keyword.get(meta, :arity, 0)
    line = Keyword.get(meta, :line, 1)
    visibility = Keyword.get(meta, :visibility, :public)

    detail =
      if visibility == :private, do: "local fn #{name}/#{arity}", else: "fn #{name}/#{arity}"

    [
      %{
        "name" => "#{name}/#{arity}",
        "kind" => 12,
        "detail" => detail,
        "range" => lsp_range(line),
        "selectionRange" => lsp_range(line)
      }
    ]
  end

  defp extract_body_item({:container, meta, body}) do
    extract_container(meta, body)
  end

  defp extract_body_item({:type_annotation, meta, _children}) do
    name = Keyword.get(meta, :name, "unknown")
    line = Keyword.get(meta, :line, 1)

    [
      %{
        "name" => name,
        "kind" => 26,
        "range" => lsp_range(line),
        "selectionRange" => lsp_range(line)
      }
    ]
  end

  # FSM transitions as symbols
  defp extract_body_item({:function_call, meta, _}) do
    case Keyword.get(meta, :name) do
      "transition" ->
        from = Keyword.get(meta, :from, "?")
        event = Keyword.get(meta, :event, "?")
        to = Keyword.get(meta, :to, "?")
        event_kind = Keyword.get(meta, :event_kind, :normal)
        line = Keyword.get(meta, :line, 1)

        suffix =
          case event_kind do
            :hard -> "!"
            :soft -> "?"
            _ -> ""
          end

        [
          %{
            "name" => "#{from} --#{event}#{suffix}--> #{to}",
            "kind" => 24,
            "detail" => "transition (#{event_kind})",
            "range" => lsp_range(line),
            "selectionRange" => lsp_range(line)
          }
        ]

      _ ->
        []
    end
  end

  defp extract_body_item(_), do: []

  defp lsp_range(line) do
    l = max(line - 1, 0)
    %{"start" => %{"line" => l, "character" => 0}, "end" => %{"line" => l, "character" => 999}}
  end
end
