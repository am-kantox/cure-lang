defmodule Cure.Compiler.BinSegmentTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser, Codegen, BeamWriter}

  # -- Lexer -----------------------------------------------------------------

  describe "lexer: `::` token" do
    test "single colon stays :colon" do
      {:ok, tokens} = Lexer.tokenize("x: Int", emit_events: false)
      assert Enum.any?(tokens, &(&1.type == :colon))
      refute Enum.any?(tokens, &(&1.type == :colon_colon))
    end

    test "double colon emits :colon_colon" do
      {:ok, tokens} = Lexer.tokenize("x::utf8", emit_events: false)
      assert Enum.any?(tokens, &(&1.type == :colon_colon))
    end
  end

  # -- Parser ----------------------------------------------------------------

  describe "parser: {:bin_segment, ...} AST" do
    test "bare integer becomes a segment with default specifiers" do
      ast = parse_expr!("<<1, 2, 3>>")
      assert {:literal, meta, segments} = ast
      assert Keyword.get(meta, :subtype) == :bytes
      assert [_, _, _] = segments
      Enum.each(segments, fn seg -> assert match?({:bin_segment, _, [_]}, seg) end)
    end

    test "::utf8 is recorded as a type specifier" do
      ast = parse_expr!(~s(<<"abc"::utf8>>))
      assert {:literal, _, [{:bin_segment, meta, [_value]}]} = ast
      assert Keyword.get(meta, :type) == :utf8
    end

    test "::binary-size(n) records type and size together" do
      ast = parse_expr!("<<payload::binary-size(n)>>")
      assert {:literal, _, [{:bin_segment, meta, [_value]}]} = ast
      assert Keyword.get(meta, :type) == :binary
      # The size expression is an AST node; here it's a variable reference.
      assert {:variable, _, "n"} = Keyword.get(meta, :size)
    end

    test "::signed-big-32 chains type, signedness, endianness, and size" do
      ast = parse_expr!("<<x::signed-big-32>>")
      assert {:literal, _, [{:bin_segment, meta, [_value]}]} = ast
      assert Keyword.get(meta, :signedness) == :signed
      assert Keyword.get(meta, :endianness) == :big
      assert {:literal, _, 32} = Keyword.get(meta, :size)
    end

    test "bare integer specifier shorthand is size(n)" do
      ast = parse_expr!("<<x::8>>")
      assert {:literal, _, [{:bin_segment, meta, [_value]}]} = ast
      assert {:literal, _, 8} = Keyword.get(meta, :size)
    end

    test "multiple segments are parsed as a list of {:bin_segment, ...} nodes" do
      ast = parse_expr!("<<tag::utf8, size::16, rest::binary>>")
      assert {:literal, _, segments} = ast
      assert [_, _, _] = segments
      types = Enum.map(segments, fn {:bin_segment, m, _} -> Keyword.get(m, :type) end)
      assert types == [:utf8, nil, :binary]
      sizes = Enum.map(segments, fn {:bin_segment, m, _} -> Keyword.get(m, :size) end)
      assert match?([nil, {:literal, _, 16}, nil], sizes)
    end
  end

  # -- Codegen + round-trip through the BEAM --------------------------------

  describe "codegen: binary construction" do
    test "<<1, 2, 3>> produces the expected binary" do
      assert eval_module_main!("""
             mod BinConst
               fn main() -> Int =
                 let bytes = <<1, 2, 3>>
                 byte_size(bytes)
             """) == 3
    end

    test "<<x::16, rest::binary>> accepts an explicit size" do
      assert eval_module_main!("""
             mod BinSize
               fn main() -> Int =
                 let v = 258
                 let bytes = <<v::16>>
                 byte_size(bytes)
             """) == 2
    end
  end

  # -- Helpers ---------------------------------------------------------------

  defp parse_expr!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  defp eval_module_main!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    {:ok, forms} = Codegen.compile_module(ast, emit_events: false)
    {:ok, module} = BeamWriter.compile_and_load(forms)
    apply(module, :main, [])
  end
end
