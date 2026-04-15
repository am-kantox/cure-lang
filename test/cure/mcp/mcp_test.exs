defmodule Cure.MCP.McpTest do
  use ExUnit.Case, async: true

  alias Cure.MCP.Server

  # ============================================================================
  # Protocol: initialize and tools/list
  # ============================================================================

  describe "MCP protocol" do
    test "initialize returns server info and capabilities" do
      resp = Server.handle_request(%{"method" => "initialize", "id" => 1, "params" => %{}})
      assert resp["id"] == 1
      assert resp["result"]["serverInfo"]["name"] == "cure-mcp"
      assert resp["result"]["capabilities"]["tools"]
    end

    test "tools/list returns tool definitions" do
      resp = Server.handle_request(%{"method" => "tools/list", "id" => 2, "params" => %{}})
      tools = resp["result"]["tools"]
      assert is_list(tools)
      assert length(tools) >= 7

      names = Enum.map(tools, & &1["name"])
      assert "compile_cure" in names
      assert "parse_cure" in names
      assert "type_check_cure" in names
      assert "analyze_fsm" in names
      assert "validate_syntax" in names
      assert "get_syntax_help" in names
      assert "get_stdlib_docs" in names
    end

    test "unknown method returns error" do
      resp = Server.handle_request(%{"method" => "unknown/thing", "id" => 3, "params" => %{}})
      assert resp["result"]["error"]
    end
  end

  # ============================================================================
  # Tool: compile_cure
  # ============================================================================

  describe "compile_cure tool" do
    test "compiles valid source" do
      resp = call_tool("compile_cure", %{"source" => "mod CompTest\n  fn x() -> Int = 42\n"})
      assert resp =~ "Compiled successfully"
      assert resp =~ "x/0"
    after
      :code.purge(:comptest)
      :code.delete(:comptest)
    end

    test "reports error for invalid source" do
      resp = call_tool("compile_cure", %{"source" => "not valid cure at all ???"})
      assert resp =~ "error" or resp =~ "Error"
    end
  end

  # ============================================================================
  # Tool: parse_cure
  # ============================================================================

  describe "parse_cure tool" do
    test "returns AST summary for valid source" do
      resp = call_tool("parse_cure", %{"source" => "mod ParseTest\n  fn foo() -> Int = 1\n"})
      assert resp =~ "module"
      assert resp =~ "foo"
    end
  end

  # ============================================================================
  # Tool: type_check_cure
  # ============================================================================

  describe "type_check_cure tool" do
    test "passes for valid typed code" do
      resp = call_tool("type_check_cure", %{"source" => "mod TypeTest\n  fn add(a: Int, b: Int) -> Int = a + b\n"})
      assert resp =~ "passed" or resp =~ "no errors"
    end
  end

  # ============================================================================
  # Tool: analyze_fsm
  # ============================================================================

  describe "analyze_fsm tool" do
    test "analyzes FSM definition" do
      source = "fsm Light\n  Red --timer--> Green\n  Green --timer--> Red\n"
      resp = call_tool("analyze_fsm", %{"source" => source})
      assert resp =~ "FSM"
      assert resp =~ "Light"
    end

    test "reports when no FSM found" do
      resp = call_tool("analyze_fsm", %{"source" => "mod NotFsm\n  fn x() -> Int = 1\n"})
      assert resp =~ "No FSM"
    end
  end

  # ============================================================================
  # Tool: validate_syntax
  # ============================================================================

  describe "validate_syntax tool" do
    test "valid syntax" do
      resp = call_tool("validate_syntax", %{"source" => "mod V\n  fn a() -> Int = 1\n"})
      assert resp =~ "valid"
    end

    test "invalid syntax" do
      resp = call_tool("validate_syntax", %{"source" => "???!!!"})
      assert resp =~ "error" or resp =~ "Error"
    end
  end

  # ============================================================================
  # Tool: get_syntax_help
  # ============================================================================

  describe "get_syntax_help tool" do
    test "returns help for functions" do
      resp = call_tool("get_syntax_help", %{"topic" => "functions"})
      assert resp =~ "fn"
      assert resp =~ "guard"
    end

    test "returns help for types" do
      resp = call_tool("get_syntax_help", %{"topic" => "types"})
      assert resp =~ "type"
    end

    test "returns help for fsm" do
      resp = call_tool("get_syntax_help", %{"topic" => "fsm"})
      assert resp =~ "fsm"
    end

    test "returns help for protocols" do
      resp = call_tool("get_syntax_help", %{"topic" => "protocols"})
      assert resp =~ "proto"
    end

    test "unknown topic lists available topics" do
      resp = call_tool("get_syntax_help", %{"topic" => "xyzzy"})
      assert resp =~ "Available topics"
    end
  end

  # ============================================================================
  # Tool: get_stdlib_docs
  # ============================================================================

  describe "get_stdlib_docs tool" do
    test "returns Std.Core source" do
      resp = call_tool("get_stdlib_docs", %{"module" => "Std.Core"})
      assert resp =~ "mod Std.Core"
      assert resp =~ "identity"
    end

    test "returns Std.List source" do
      resp = call_tool("get_stdlib_docs", %{"module" => "Std.List"})
      assert resp =~ "mod Std.List"
      assert resp =~ "map"
    end

    test "unknown module lists available" do
      resp = call_tool("get_stdlib_docs", %{"module" => "Std.Unknown"})
      assert resp =~ "Available modules"
    end
  end

  # ============================================================================
  # Helper
  # ============================================================================

  defp call_tool(name, args) do
    resp =
      Server.handle_request(%{
        "method" => "tools/call",
        "id" => System.unique_integer([:positive]),
        "params" => %{"name" => name, "arguments" => args}
      })

    resp["result"]["content"] |> hd() |> Map.get("text")
  end
end
