defmodule Cure.MCP.Server do
  @moduledoc """
  Model Context Protocol (MCP) server for the Cure programming language.

  Provides AI tool integration via JSON-RPC 2.0 over stdio (newline-delimited).

  ## Tools

  - `compile_cure` -- compile Cure source code, return result or errors
  - `parse_cure` -- parse source and return AST summary
  - `type_check_cure` -- type-check source, return errors/warnings
  - `analyze_fsm` -- analyze an FSM definition (states, transitions, verification)
  - `validate_syntax` -- quick syntax validation (lex + parse only)
  - `get_syntax_help` -- get help on a Cure syntax topic
  - `get_examples` -- list or show example programs
  - `get_stdlib_docs` -- get documentation for a stdlib module

  ## Usage

      mix cure.mcp
  """

  alias Cure.Compiler.{Lexer, Parser}

  @tools [
    %{
      "name" => "compile_cure",
      "description" =>
        "Compile Cure source code to BEAM bytecode. Returns the module name on success or error details.",
      "inputSchema" => %{
        "type" => "object",
        "properties" => %{"source" => %{"type" => "string", "description" => "Cure source code"}},
        "required" => ["source"]
      }
    },
    %{
      "name" => "parse_cure",
      "description" => "Parse Cure source code and return a summary of the AST structure.",
      "inputSchema" => %{
        "type" => "object",
        "properties" => %{"source" => %{"type" => "string", "description" => "Cure source code"}},
        "required" => ["source"]
      }
    },
    %{
      "name" => "type_check_cure",
      "description" => "Type-check Cure source code. Returns errors and warnings.",
      "inputSchema" => %{
        "type" => "object",
        "properties" => %{"source" => %{"type" => "string", "description" => "Cure source code"}},
        "required" => ["source"]
      }
    },
    %{
      "name" => "analyze_fsm",
      "description" => "Analyze a Cure FSM definition. Returns states, transitions, and verification results.",
      "inputSchema" => %{
        "type" => "object",
        "properties" => %{"source" => %{"type" => "string", "description" => "Cure FSM source code"}},
        "required" => ["source"]
      }
    },
    %{
      "name" => "validate_syntax",
      "description" => "Quick syntax validation -- lex and parse only, no type checking.",
      "inputSchema" => %{
        "type" => "object",
        "properties" => %{"source" => %{"type" => "string", "description" => "Cure source code"}},
        "required" => ["source"]
      }
    },
    %{
      "name" => "get_syntax_help",
      "description" =>
        "Get help on a Cure syntax topic (functions, types, fsm, protocols, pattern_matching, modules, records).",
      "inputSchema" => %{
        "type" => "object",
        "properties" => %{"topic" => %{"type" => "string", "description" => "Syntax topic name"}},
        "required" => ["topic"]
      }
    },
    %{
      "name" => "get_stdlib_docs",
      "description" => "Get documentation for a Cure standard library module (Std.Core, Std.List, Std.Math, etc.).",
      "inputSchema" => %{
        "type" => "object",
        "properties" => %{"module" => %{"type" => "string", "description" => "Module name, e.g. Std.List"}},
        "required" => ["module"]
      }
    }
  ]

  # -- Public API --------------------------------------------------------------

  @doc "Start the MCP server (blocking, reads from stdio)."
  def start do
    Application.ensure_all_started(:cure)
    :io.setopts(:standard_io, binary: true, encoding: :latin1)
    loop()
  end

  @doc """
  Handle a single JSON-RPC request map and return the response map.

  Used for testing without the stdio loop.
  """
  @spec handle_request(map()) :: map()
  def handle_request(%{"method" => method, "id" => id} = req) do
    params = Map.get(req, "params", %{})
    result = dispatch(method, params)
    %{"jsonrpc" => "2.0", "id" => id, "result" => result}
  end

  def handle_request(%{"method" => method} = req) do
    params = Map.get(req, "params", %{})
    _result = dispatch(method, params)
    nil
  end

  # -- Stdio Loop --------------------------------------------------------------

  defp loop do
    case IO.gets("") do
      :eof ->
        :ok

      {:error, _} ->
        :ok

      line when is_binary(line) ->
        line = String.trim(line)

        if line != "" do
          case safe_decode(line) do
            {:ok, request} ->
              response = handle_request(request)
              if response, do: send_response(response)

            :error ->
              :ok
          end
        end

        loop()
    end
  end

  defp send_response(response) do
    json = :json.encode(response) |> IO.iodata_to_binary()
    IO.puts(json)
  end

  defp safe_decode(binary) do
    {:ok, :json.decode(binary)}
  rescue
    _ -> :error
  end

  # -- Method Dispatch ---------------------------------------------------------

  defp dispatch("initialize", _params) do
    %{
      "protocolVersion" => "2024-11-05",
      "capabilities" => %{"tools" => %{"listChanged" => false}},
      "serverInfo" => %{"name" => "cure-mcp", "version" => "0.1.0"}
    }
  end

  defp dispatch("tools/list", _params) do
    %{"tools" => @tools}
  end

  defp dispatch("tools/call", %{"name" => name, "arguments" => args}) do
    tool_result = call_tool(name, args)
    %{"content" => [%{"type" => "text", "text" => tool_result}]}
  end

  defp dispatch("tools/call", %{"name" => name}) do
    tool_result = call_tool(name, %{})
    %{"content" => [%{"type" => "text", "text" => tool_result}]}
  end

  defp dispatch(_method, _params), do: %{"error" => "unknown method"}

  # -- Tool Implementations ----------------------------------------------------

  defp call_tool("compile_cure", %{"source" => source}) do
    case Cure.Compiler.compile_and_load(source, emit_events: false) do
      {:ok, module} ->
        exports =
          module.module_info(:exports)
          |> Enum.reject(fn {n, _} -> n == :module_info end)
          |> Enum.map(fn {n, a} -> "#{n}/#{a}" end)
          |> Enum.join(", ")

        "Compiled successfully: #{module}\nExports: #{exports}"

      {:error, reason} ->
        "Compilation error: #{inspect(reason)}"
    end
  end

  defp call_tool("parse_cure", %{"source" => source}) do
    with {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false) do
      summarize_ast(ast)
    else
      {:error, reason} -> "Parse error: #{inspect(reason)}"
    end
  end

  defp call_tool("type_check_cure", %{"source" => source}) do
    with {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false) do
      case Cure.Types.Checker.check_module(ast, emit_events: false) do
        {:ok, _} -> "Type check passed: no errors."
        {:error, errors} -> "Type errors:\n" <> format_errors(errors)
      end
    else
      {:error, reason} -> "Parse error: #{inspect(reason)}"
    end
  end

  defp call_tool("analyze_fsm", %{"source" => source}) do
    with {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false) do
      fsm_ast = find_fsm(ast)

      if fsm_ast do
        case Cure.FSM.Verifier.verify(fsm_ast, emit_events: false) do
          {:ok, _} -> "FSM verification passed.\n" <> describe_fsm(fsm_ast)
          {:error, errors} -> "FSM issues:\n" <> format_errors(errors)
        end
      else
        "No FSM definition found in the source."
      end
    else
      {:error, reason} -> "Parse error: #{inspect(reason)}"
    end
  end

  defp call_tool("validate_syntax", %{"source" => source}) do
    with {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, _ast} <- Parser.parse(tokens, emit_events: false) do
      "Syntax is valid. #{length(tokens)} tokens parsed."
    else
      {:error, reason} -> "Syntax error: #{inspect(reason)}"
    end
  end

  defp call_tool("get_syntax_help", %{"topic" => topic}) do
    syntax_help(topic)
  end

  defp call_tool("get_stdlib_docs", %{"module" => module}) do
    stdlib_docs(module)
  end

  defp call_tool(name, _args), do: "Unknown tool: #{name}"

  # -- AST Summary -------------------------------------------------------------

  defp summarize_ast({:container, meta, body}) do
    type = Keyword.get(meta, :container_type, :unknown)
    name = Keyword.get(meta, :name, "unnamed")

    items =
      Enum.map(body, fn
        {:function_def, m, _} -> "  fn #{Keyword.get(m, :name)}/#{Keyword.get(m, :arity, 0)}"
        {:container, m, _} -> "  #{Keyword.get(m, :container_type)} #{Keyword.get(m, :name)}"
        _ -> "  (other)"
      end)

    "#{type} #{name}\n#{Enum.join(items, "\n")}"
  end

  defp summarize_ast({:block, _, children}) do
    Enum.map_join(children, "\n\n", &summarize_ast/1)
  end

  defp summarize_ast(_), do: "(expression)"

  # -- FSM Helpers -------------------------------------------------------------

  defp find_fsm({:container, meta, _body} = ast) do
    if Keyword.get(meta, :container_type) == :fsm, do: ast, else: nil
  end

  defp find_fsm({:block, _, children}) do
    Enum.find_value(children, &find_fsm/1)
  end

  defp find_fsm(_), do: nil

  defp describe_fsm({:container, meta, transitions}) do
    name = Keyword.get(meta, :name, "unnamed")

    trans =
      Enum.flat_map(transitions, fn
        {:function_call, m, _} ->
          if Keyword.get(m, :name) == "transition" do
            ["  #{Keyword.get(m, :from)} --#{Keyword.get(m, :event)}--> #{Keyword.get(m, :to)}"]
          else
            []
          end

        _ ->
          []
      end)

    "FSM: #{name}\nTransitions:\n#{Enum.join(trans, "\n")}"
  end

  # -- Error Formatting --------------------------------------------------------

  defp format_errors(errors) when is_list(errors) do
    Enum.map_join(errors, "\n", fn
      {type, msg, _opts} -> "  #{type}: #{msg}"
      other -> "  #{inspect(other)}"
    end)
  end

  defp format_errors(other), do: inspect(other)

  # -- Syntax Help -------------------------------------------------------------

  defp syntax_help("functions") do
    """
    === Functions ===
    # Single-line function
    fn add(a: Int, b: Int) -> Int = a + b

    # Multi-line function body
    fn compute(x: Int) -> Int =
      let y = x * 2
      y + 1

    # Multi-clause function
    fn factorial(n: Int) -> Int
      | 0 -> 1
      | n -> n * factorial(n - 1)

    # Function with guard
    fn abs(x: Int) -> Int when x >= 0 = x

    # Private function
    local fn helper(x: Int) -> Int = x * 2

    # External function (FFI)
    @extern(:erlang, :abs, 1)
    fn abs(x: Int) -> Int
    """
  end

  defp syntax_help("types") do
    """
    === Types ===
    # ADT (sum type)
    type Color = Red | Green | Blue
    type Option(T) = Some(T) | None

    # Refinement type
    type NonZero = {x: Int | x != 0}
    type Positive = {x: Int | x > 0}

    # Type alias
    type Name = String
    """
  end

  defp syntax_help("fsm") do
    """
    === Finite State Machines ===
    fsm TrafficLight
      Red    --timer-->     Green
      Green  --timer-->     Yellow
      Yellow --timer-->     Red
      *      --emergency--> Red

    # * is a wildcard matching any state
    # Compile with: mix cure.compile traffic.cure
    """
  end

  defp syntax_help("protocols") do
    """
    === Protocols ===
    proto Show(T)
      fn show(x: T) -> String

    impl Show for Int
      fn show(x: Int) -> String = Std.String.from_int(x)

    impl Show for Bool
      fn show(x: Bool) -> String = if x then "true" else "false"
    """
  end

  defp syntax_help("pattern_matching") do
    """
    === Pattern Matching ===
    # Match expression
    match x
      Ok(v)    -> v
      Error(e) -> default

    # List patterns
    match list
      []       -> "empty"
      [h | t]  -> "has head"

    # Boolean match
    match flag
      true  -> "yes"
      false -> "no"
    """
  end

  defp syntax_help("modules") do
    """
    === Modules ===
    mod MyApp.Math
      fn add(a: Int, b: Int) -> Int = a + b
      fn mul(a: Int, b: Int) -> Int = a * b

    # Modules use indentation (no do...end)
    # All functions are public by default
    # Use 'local fn' for private functions
    """
  end

  defp syntax_help(_topic) do
    "Available topics: functions, types, fsm, protocols, pattern_matching, modules"
  end

  # -- Stdlib Docs -------------------------------------------------------------

  defp stdlib_docs("Std.Core"), do: read_stdlib_file("core")
  defp stdlib_docs("Std.List"), do: read_stdlib_file("list")
  defp stdlib_docs("Std.Math"), do: read_stdlib_file("math")
  defp stdlib_docs("Std.String"), do: read_stdlib_file("string")
  defp stdlib_docs("Std.Io"), do: read_stdlib_file("io")
  defp stdlib_docs("Std.Pair"), do: read_stdlib_file("pair")
  defp stdlib_docs("Std.Show"), do: read_stdlib_file("show")
  defp stdlib_docs("Std.System"), do: read_stdlib_file("system")
  defp stdlib_docs("Std.Fsm"), do: read_stdlib_file("fsm")

  defp stdlib_docs(_) do
    "Available modules: Std.Core, Std.List, Std.Math, Std.String, Std.Io, Std.Pair, Std.Show, Std.System, Std.Fsm"
  end

  defp read_stdlib_file(name) do
    path = Path.join(["lib", "std", "#{name}.cure"])

    case File.read(path) do
      {:ok, content} -> content
      {:error, _} -> "Source file not found: #{path}"
    end
  end
end
