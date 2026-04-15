defmodule Cure.LSP.Server do
  @moduledoc """
  Language Server Protocol implementation for Cure.

  Implements the LSP over stdio, providing:
  - Real-time diagnostics (compile errors) on document changes
  - Hover information (function signatures, types)
  - Document synchronization (full sync mode)

  ## Usage

  Start from the command line:

      mix cure.lsp

  Or programmatically:

      {:ok, pid} = Cure.LSP.Server.start_link()
  """

  use GenServer

  alias Cure.LSP.Transport
  alias Cure.Compiler.{Lexer, Parser}

  defstruct [
    :reader_pid,
    initialized: false,
    documents: %{},
    ast_cache: %{},
    buffer: ""
  ]

  # -- Public API --------------------------------------------------------------

  @doc "Start the LSP server."
  def start_link(opts \\ []) do
    GenServer.start_link(__MODULE__, opts, name: __MODULE__)
  end

  @doc """
  Process a raw incoming message (used by the stdin reader or tests).
  """
  def handle_raw_message(message) when is_map(message) do
    GenServer.cast(__MODULE__, {:message, message})
  end

  @doc """
  Process a raw message directly, returning the server's response action.

  Used for testing without the GenServer.
  """
  @spec process_message(map(), map()) :: {map(), [map()]}
  def process_message(message, state) do
    method = Map.get(message, "method")
    id = Map.get(message, "id")
    params = Map.get(message, "params", %{})

    do_handle(method, id, params, state)
  end

  # -- GenServer Callbacks -----------------------------------------------------

  @impl true
  def init(_opts) do
    # Start the stdin reader process that reads LSP frames and sends messages
    server = self()

    reader =
      spawn_link(fn ->
        lsp_reader_loop(server)
      end)

    {:ok, %__MODULE__{reader_pid: reader}}
  end

  @impl true
  def handle_cast({:message, message}, state) do
    {new_state, _responses} = process_message(message, state)
    {:noreply, struct(__MODULE__, new_state)}
  end

  @impl true
  def handle_info({:lsp_message, message}, state) do
    {new_state, _} = process_message(message, Map.from_struct(state))
    {:noreply, struct(__MODULE__, new_state)}
  end

  def handle_info(_msg, state), do: {:noreply, state}

  # -- Message Dispatch --------------------------------------------------------

  defp do_handle("initialize", id, _params, state) do
    result = %{
      "capabilities" => %{
        "textDocumentSync" => %{
          "openClose" => true,
          "change" => 1,
          "save" => %{"includeText" => true}
        },
        "hoverProvider" => true,
        "definitionProvider" => true,
        "documentSymbolProvider" => true,
        "codeActionProvider" => %{
          "codeActionKinds" => ["quickfix"]
        },
        "completionProvider" => %{
          "triggerCharacters" => [".", ":"]
        }
      },
      "serverInfo" => %{
        "name" => "cure-lsp",
        "version" => "0.1.0"
      }
    }

    Transport.send_response(id, result)
    {Map.put(state, :initialized, true), []}
  end

  defp do_handle("initialized", _id, _params, state) do
    {state, []}
  end

  defp do_handle("shutdown", id, _params, state) do
    Transport.send_response(id, nil)
    {state, []}
  end

  defp do_handle("exit", _id, _params, state) do
    System.halt(0)
    {state, []}
  end

  defp do_handle("textDocument/didOpen", _id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    text = Map.get(td, "text", "")

    docs = Map.get(state, :documents, %{})
    state = Map.put(state, :documents, Map.put(docs, uri, text))

    diagnostics = compute_diagnostics(uri, text)
    publish_diagnostics(uri, diagnostics)

    {state, diagnostics}
  end

  defp do_handle("textDocument/didChange", _id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    version = Map.get(td, "version")
    changes = Map.get(params, "contentChanges", [])

    text =
      case changes do
        [%{"text" => full_text} | _] -> full_text
        _ -> Map.get(Map.get(state, :documents, %{}), uri, "")
      end

    docs = Map.get(state, :documents, %{})
    state = Map.put(state, :documents, Map.put(docs, uri, text))

    # Check AST cache -- skip reparse if version unchanged
    cache = Map.get(state, :ast_cache, %{})
    cached_version = get_in(cache, [uri, :version])

    if cached_version == version and version != nil do
      # Same version, skip diagnostics
      {state, []}
    else
      diagnostics = compute_diagnostics(uri, text)
      publish_diagnostics(uri, diagnostics)

      # Update cache
      cache = Map.put(cache, uri, %{version: version, diagnostics: diagnostics})
      state = Map.put(state, :ast_cache, cache)

      {state, diagnostics}
    end
  end

  defp do_handle("textDocument/didClose", _id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    docs = Map.get(state, :documents, %{})
    state = Map.put(state, :documents, Map.delete(docs, uri))

    # Clear diagnostics
    publish_diagnostics(uri, [])
    {state, []}
  end

  defp do_handle("textDocument/didSave", _id, _params, state) do
    {state, []}
  end

  defp do_handle("textDocument/hover", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    pos = Map.get(params, "position", %{})
    line = Map.get(pos, "line", 0)
    char = Map.get(pos, "character", 0)

    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")
    result = compute_hover(text, line, char)

    Transport.send_response(id, result)
    {state, []}
  end

  defp do_handle("textDocument/completion", id, _params, state) do
    items = keyword_completions()
    Transport.send_response(id, items)
    {state, []}
  end

  defp do_handle("textDocument/definition", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    pos = Map.get(params, "position", %{})
    line = Map.get(pos, "line", 0)
    char = Map.get(pos, "character", 0)

    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")
    result = find_definition(text, uri, line, char)

    Transport.send_response(id, result)
    {state, []}
  end

  defp do_handle("textDocument/documentSymbol", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    docs = Map.get(state, :documents, %{})
    text = Map.get(docs, uri, "")

    symbols = compute_symbols(text)
    Transport.send_response(id, symbols)
    {state, []}
  end

  defp do_handle("textDocument/codeAction", id, params, state) do
    td = Map.get(params, "textDocument", %{})
    uri = Map.get(td, "uri", "")
    context = Map.get(params, "context", %{})
    diagnostics = Map.get(context, "diagnostics", [])

    actions = compute_code_actions(uri, diagnostics)
    Transport.send_response(id, actions)
    {state, []}
  end

  defp do_handle(_method, _id, _params, state) do
    {state, []}
  end

  # -- Diagnostics -------------------------------------------------------------

  @doc false
  def compute_diagnostics(_uri, text) do
    case Lexer.tokenize(text, emit_events: false) do
      {:ok, tokens} ->
        case Parser.parse(tokens, emit_events: false) do
          {:ok, _ast} -> []
          {:error, errors} -> Enum.map(errors, &format_diagnostic/1)
        end

      {:error, reason} ->
        [format_diagnostic(reason)]
    end
  end

  defp format_diagnostic({type, msg, opts}) when is_list(opts) do
    line = Keyword.get(opts, :line, 1) - 1
    message = elem_or("", 1, {type, msg, opts})

    %{
      "range" => %{
        "start" => %{"line" => max(line, 0), "character" => 0},
        "end" => %{"line" => max(line, 0), "character" => 999}
      },
      "severity" => 1,
      "source" => "cure",
      "message" => to_string(message)
    }
  end

  defp format_diagnostic({type, msg, line, _col}) do
    %{
      "range" => %{
        "start" => %{"line" => max(line - 1, 0), "character" => 0},
        "end" => %{"line" => max(line - 1, 0), "character" => 999}
      },
      "severity" => 1,
      "source" => "cure",
      "message" => "#{type}: #{msg}"
    }
  end

  defp format_diagnostic(other) do
    %{
      "range" => %{
        "start" => %{"line" => 0, "character" => 0},
        "end" => %{"line" => 0, "character" => 999}
      },
      "severity" => 1,
      "source" => "cure",
      "message" => inspect(other)
    }
  end

  defp elem_or(default, index, tuple) when is_tuple(tuple) do
    if tuple_size(tuple) > index, do: elem(tuple, index), else: default
  end

  defp publish_diagnostics(uri, diagnostics) do
    Transport.send_notification("textDocument/publishDiagnostics", %{
      "uri" => uri,
      "diagnostics" => diagnostics
    })
  end

  # -- Hover -------------------------------------------------------------------

  defp compute_hover(text, line, _char) do
    # Get the line content and provide basic info
    lines = String.split(text, "\n")
    target_line = Enum.at(lines, line, "")

    cond do
      String.contains?(target_line, "fn ") ->
        # Attempt to infer effects for display
        effect_info = infer_hover_effects(target_line)

        hover_text =
          if effect_info != "" do
            "```cure\n#{String.trim(target_line)}\n```\n\n**Effects:** #{effect_info}"
          else
            "```cure\n#{String.trim(target_line)}\n```"
          end

        %{
          "contents" => %{
            "kind" => "markdown",
            "value" => hover_text
          }
        }

      String.contains?(target_line, "mod ") ->
        %{
          "contents" => %{
            "kind" => "markdown",
            "value" => "**Module definition**\n```cure\n#{String.trim(target_line)}\n```"
          }
        }

      String.contains?(target_line, "fsm ") ->
        %{
          "contents" => %{
            "kind" => "markdown",
            "value" => "**FSM definition**\n```cure\n#{String.trim(target_line)}\n```"
          }
        }

      true ->
        nil
    end
  end

  defp infer_hover_effects(line) do
    cond do
      String.contains?(line, "! ") ->
        case Regex.run(~r/!\s+(.+?)(?:\s+when|\s+=|$)/, line) do
          [_, effects] -> effects
          _ -> ""
        end

      Enum.any?(["println", "print", "put_chars"], &String.contains?(line, &1)) ->
        "Io"

      String.contains?(line, "throw") ->
        "Exception"

      String.contains?(line, "spawn") ->
        "Spawn"

      true ->
        ""
    end
  end

  # -- Go-to-Definition --------------------------------------------------------

  defp find_definition(text, uri, line, _char) do
    lines = String.split(text, "\n")
    target_line = Enum.at(lines, line, "")

    # Extract the word at the cursor position
    word = extract_word(target_line)

    if word != "" do
      # Search all lines for a function definition matching the word
      definition_line =
        Enum.find_index(lines, fn l ->
          String.contains?(l, "fn #{word}(") or String.contains?(l, "fn #{word} ")
        end)

      if definition_line do
        %{
          "uri" => uri,
          "range" => %{
            "start" => %{"line" => definition_line, "character" => 0},
            "end" => %{"line" => definition_line, "character" => 999}
          }
        }
      else
        nil
      end
    else
      nil
    end
  end

  defp extract_word(line) do
    # Extract the first identifier-like word from the line
    case Regex.run(~r/\b([a-z_][a-z0-9_]*)\s*\(/, line) do
      [_, word] ->
        word

      _ ->
        case Regex.run(~r/\b([a-z_][a-z0-9_]*)/, String.trim(line)) do
          [_, word] -> word
          _ -> ""
        end
    end
  end

  # -- Document Symbols --------------------------------------------------------

  defp compute_symbols(text) do
    with {:ok, tokens} <- Lexer.tokenize(text, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false) do
      Cure.LSP.Symbols.extract(ast)
    else
      _ -> []
    end
  end

  # -- Code Actions ------------------------------------------------------------

  @doc false
  def compute_code_actions(_uri, diagnostics) do
    Enum.flat_map(diagnostics, fn diag ->
      message = Map.get(diag, "message", "")

      cond do
        String.contains?(message, "not exhaustive") ->
          [
            %{
              "title" => "Add wildcard pattern (_ -> ...)",
              "kind" => "quickfix",
              "diagnostics" => [diag]
            }
          ]

        String.contains?(message, "undefined") or String.contains?(message, "unbound") ->
          # Try to suggest similar names
          case Regex.run(~r/'([^']+)'/, message) do
            [_, name] ->
              candidates = ~w(fn mod let if match type proto impl use)

              case Cure.Compiler.Errors.suggest(name, candidates) do
                nil ->
                  []

                suggestion ->
                  [
                    %{
                      "title" => "Did you mean '#{suggestion}'?",
                      "kind" => "quickfix",
                      "diagnostics" => [diag]
                    }
                  ]
              end

            _ ->
              []
          end

        true ->
          []
      end
    end)
  end

  # -- Completions -------------------------------------------------------------

  defp keyword_completions do
    keywords =
      ~w(fn mod rec fsm proto impl type let if then else elif match return throw try catch finally use local when where)

    Enum.map(keywords, fn kw ->
      %{
        "label" => kw,
        "kind" => 14,
        "detail" => "Cure keyword"
      }
    end)
  end

  # -- Stdin Reader (Content-Length aware) -------------------------------------

  defp lsp_reader_loop(server) do
    case read_lsp_message() do
      {:ok, message} ->
        send(server, {:lsp_message, message})
        lsp_reader_loop(server)

      :eof ->
        :ok

      {:error, _} ->
        :ok
    end
  end

  defp read_lsp_message do
    # Read headers until blank line (\r\n\r\n)
    case read_headers(%{}) do
      {:ok, headers} ->
        content_length = Map.get(headers, "content-length", "0") |> String.to_integer()

        if content_length > 0 do
          case IO.binread(:stdio, content_length) do
            data when is_binary(data) ->
              case safe_json_decode(data) do
                {:ok, msg} -> {:ok, msg}
                :error -> {:error, :json_decode}
              end

            _ ->
              :eof
          end
        else
          {:error, :no_content_length}
        end

      :eof ->
        :eof
    end
  end

  defp read_headers(acc) do
    case IO.binread(:stdio, :line) do
      line when is_binary(line) ->
        trimmed = String.trim_trailing(line, "\r\n") |> String.trim_trailing("\n")

        cond do
          # Blank line = end of headers
          trimmed == "" or trimmed == "\r" ->
            {:ok, acc}

          # Header line: Key: Value
          String.contains?(trimmed, ":") ->
            [key | rest] = String.split(trimmed, ":", parts: 2)
            value = Enum.join(rest, ":") |> String.trim()
            read_headers(Map.put(acc, String.downcase(String.trim(key)), value))

          true ->
            read_headers(acc)
        end

      _ ->
        :eof
    end
  end

  defp safe_json_decode(binary) do
    {:ok, :json.decode(binary)}
  rescue
    _ -> :error
  end
end
