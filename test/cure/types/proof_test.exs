defmodule Cure.Types.ProofTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler

  defp compile(source) do
    Compiler.compile_and_load(source, emit_events: false)
  end

  describe "proof containers" do
    test "compile as modules with proof-shaped functions" do
      source = """
      proof ProofTest.Basic
        fn id_law(_n: Int) -> Eq(Int, n, n) = :cure_refl
      """

      {:ok, mod} = compile(source)
      assert mod.id_law(42) == :cure_refl
    end

    test "allow multiple propositions in one container" do
      source = """
      proof ProofTest.Several
        fn plus_zero(_n: Int) -> Eq(Int, n, n) = :cure_refl
        fn zero_plus(_n: Int) -> Eq(Int, n, n) = :cure_refl
      """

      {:ok, mod} = compile(source)
      assert mod.plus_zero(5) == :cure_refl
      assert mod.zero_plus(5) == :cure_refl
    end
  end

  describe "proof-shape discipline (E026)" do
    test "rejects non-proof return types" do
      source = """
      proof ProofTest.Bad
        fn meaning() -> Int = 42
      """

      # The checker rejects `meaning/0` because Int is not a proof shape.
      # compile_and_load runs without check_types by default, so we call
      # the type checker directly here.
      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(source, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)

      assert {:error, errors} = Cure.Types.Checker.check_module(ast, emit_events: false)

      assert Enum.any?(errors, fn
               {:proof_shape_mismatch, msg, _} -> msg =~ "E026"
               _ -> false
             end)
    end
  end
end
