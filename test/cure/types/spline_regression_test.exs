defmodule Cure.Types.SplineRegressionTest do
  use ExUnit.Case, async: true

  @moduledoc """
  Locks in the behaviour that `./cure check` must accept
  `examples/cure_spline/cure_src/spline.cure` without raising any
  diagnostics. Before this regression the checker produced 19 false
  positives driven by three distinct bugs: missing generic type-variable
  support, `{:list, :any}` for empty-list literals that refused to join
  with concrete element types, and a `join/2` that collapsed structural
  types to `:any`.
  """

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Types.Checker

  @spline_path "examples/cure_spline/cure_src/spline.cure"

  test "spline.cure type-checks without false positives" do
    source = File.read!(@spline_path)

    {:ok, tokens} = Lexer.tokenize(source, file: @spline_path, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, file: @spline_path, emit_events: false)

    assert {:ok, _} = Checker.check_module(ast, file: @spline_path, emit_events: false)
  end

  test "spline.cure compiles through the full pipeline with type checking on" do
    source = File.read!(@spline_path)

    assert {:ok, module, _warnings} =
             Cure.Compiler.compile_string(source,
               file: @spline_path,
               output_dir: "_build/cure/ex_ebin",
               emit_events: false
             )

    assert module == :"Cure.Spline"
  end
end
