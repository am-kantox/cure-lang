defmodule Cure.Compiler.MatchSpecTest do
  @moduledoc """
  Spec-conformance tests for the `match` construct as defined in
  `docs/MATCH.md` (Version 1.0.0). Mirrors Appendix A of the spec
  and exercises:

    * lexer recognition of `match` and `when`;
    * parser block / inline grammar (MATCH §4);
    * pattern shapes (MATCH §5) round-tripping through the printer;
    * canonical block printing (MATCH §9);
    * codegen end-to-end via `Cure.Compiler.compile_and_load/2`;
    * spec-mandated diagnostic catalogue entries (E032, E033, E073-E075).

  Pickup-specific behaviour and the `pickup`/`match` companion rules
  live in `Cure.Compiler.PickupTest`.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler
  alias Cure.Compiler.{Errors, Lexer, Parser, Printer}

  @out_dir "_build/cure/match_spec_test_out"

  setup_all do
    File.mkdir_p!(@out_dir)
    :ok
  end

  # ── §3 Lexical ───────────────────────────────────────────────────────────

  describe "lexer recognition" do
    test "`match` and `when` are reserved keywords" do
      {:ok, tokens} = Lexer.tokenize("match when", emit_events: false)
      kinds = for tok <- tokens, tok.type == :keyword, do: tok.value
      assert :match in kinds
      assert :when in kinds
    end
  end

  # ── §4 Grammar ───────────────────────────────────────────────────────────

  describe "parser grammar (MATCH §4)" do
    test "inline form parses to {:pattern_match, _, [scrutinee | arms]}" do
      assert {:ok, {:pattern_match, _, [_scrut, arm1, arm2]}} =
               parse("match x { 0 -> :zero, _ -> :other }")

      assert {:match_arm, _, _} = arm1
      assert {:match_arm, _, _} = arm2
    end

    test "block form parses identically to the inline form, modulo positions" do
      block = """
      match x
        0 -> :zero
        _ -> :other
      """

      inline = "match x { 0 -> :zero, _ -> :other }"

      assert {:ok, ast_block} = parse(block)
      assert {:ok, ast_inline} = parse(inline)
      assert strip_positions(ast_block) == strip_positions(ast_inline)
    end

    test "guards are parsed as `pat when g -> body`" do
      assert {:ok, {:pattern_match, _, [_, arm]}} =
               parse("match x { x when x > 0 -> x }")

      {:match_arm, meta, _body} = arm
      assert Keyword.get(meta, :pattern) != nil
      assert Keyword.get(meta, :guard) != nil
    end
  end

  # ── §6-7 Static & Dynamic semantics through codegen ──────────────────────

  describe "selection semantics (MATCH §7.1)" do
    test "first matching pattern wins" do
      source = """
      mod M
        fn classify(x: Int) -> Atom =
          match x
            0 -> :zero
            1 -> :one
            _ -> :other
      """

      {:ok, mod} = compile_and_load(source)
      assert :zero = mod.classify(0)
      assert :one = mod.classify(1)
      assert :other = mod.classify(42)
    end

    test "guards filter clauses (MATCH §7.1)" do
      source = """
      mod M
        fn sign(x: Int) -> Atom =
          match x
            n when n > 0 -> :positive
            n when n < 0 -> :negative
            _ -> :zero
      """

      {:ok, mod} = compile_and_load(source)
      assert :positive = mod.sign(5)
      assert :negative = mod.sign(-1)
      assert :zero = mod.sign(0)
    end

    test "ADT constructors dispatch on shape (MATCH §5.10)" do
      # The runtime representation of an ADT constructor is
      # implementation-defined, so we drive the Cure-side functions
      # rather than fabricating tagged tuples by hand.
      source = """
      mod M
        type Shape = Circle(Int) | Square(Int)

        fn make_circle(r: Int) -> Shape = Circle(r)
        fn make_square(s: Int) -> Shape = Square(s)

        fn area(s: Shape) -> Int =
          match s
            Circle(r) -> r * r * 3
            Square(side) -> side * side
      """

      {:ok, mod} = compile_and_load(source)
      assert mod.area(mod.make_circle(2)) == 12
      assert mod.area(mod.make_square(3)) == 9
    end
  end

  # ── §9 Formatting / Printer ──────────────────────────────────────────────

  describe "canonical block printer (MATCH §9)" do
    test "block form survives a parse -> print -> parse round-trip" do
      source = "match x { 0 -> :zero, _ -> :other }"
      {:ok, ast} = parse(source)

      printed = Printer.quoted_to_string(ast)
      assert printed =~ ~r/\Amatch x\n/
      assert printed =~ ~r/0\s+-> :zero/
      assert printed =~ ~r/_\s+-> :other/

      {:ok, re_ast} = parse(printed)
      assert strip_positions(ast) == strip_positions(re_ast)
    end

    test "block with guards aligns the head text including the `when` clause" do
      source = "match x { y when y > 0 -> :pos, _ -> :other }"
      {:ok, ast} = parse(source)

      printed = Printer.quoted_to_string(ast)
      # The clause-head (`y when y > 0`) is wider than `_`, so the
      # narrow head must be padded out to match the wide one.
      assert printed =~ ~r/y when y > 0 -> :pos/
      assert printed =~ ~r/_\s+-> :other/
    end
  end

  # ── §20 Diagnostics catalogue ────────────────────────────────────────────

  describe "spec-mandated diagnostic catalogue" do
    # E032 = W-MATCH-UNREACHABLE, E033 = E-MATCH-BRANCH-MISMATCH per
    # the spec rotation introduced alongside the v1.0.0 specs.
    @match_codes ~w(E032 E033 E073 E074 E075)

    test "every MATCH diagnostic code is registered" do
      Enum.each(@match_codes, fn code ->
        assert {:ok, text} = Errors.explain(code), "missing explainer for #{code}"
        assert text =~ "MATCH" or text =~ "match"
      end)
    end
  end

  # ── §10 Interaction with `pickup` ────────────────────────────────────────

  describe "interaction with pickup" do
    test "pickup nested inside a match arm parses and compiles" do
      source = """
      mod M
        fn label(x: Int) -> Atom =
          match x
            0 -> :zero
            n ->
              pickup
                n > 0 -> :positive
                else  -> :negative
      """

      {:ok, mod} = compile_and_load(source)
      assert :zero = mod.label(0)
      assert :positive = mod.label(7)
      assert :negative = mod.label(-3)
    end

    test "match nested inside a pickup body parses and compiles" do
      source = """
      mod M
        type Pair = Both(Int, Int) | One(Int)

        fn make_both(a: Int, b: Int) -> Pair = Both(a, b)
        fn make_one(a: Int) -> Pair = One(a)

        fn first(p: Pair) -> Int =
          pickup
            true ->
              match p
                Both(x, _y) -> x
                One(x) -> x
      """

      {:ok, mod} = compile_and_load(source)
      assert mod.first(mod.make_both(5, 7)) == 5
      assert mod.first(mod.make_one(9)) == 9
    end
  end

  # ── Helpers ──────────────────────────────────────────────────────────────

  defp parse(source) do
    with {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false) do
      {:ok, ast}
    end
  end

  defp compile_and_load(source) do
    Compiler.compile_and_load(source, file: "match_spec_test.cure", emit_events: false)
  end

  defp strip_positions({tag, meta, children}) when is_list(meta) do
    meta =
      meta
      |> Keyword.delete(:line)
      |> Keyword.delete(:col)
      |> Keyword.delete(:column)
      |> Enum.map(fn {k, v} -> {k, strip_positions(v)} end)

    {tag, meta, strip_positions(children)}
  end

  defp strip_positions(list) when is_list(list), do: Enum.map(list, &strip_positions/1)

  defp strip_positions(tuple) when is_tuple(tuple) do
    tuple |> Tuple.to_list() |> Enum.map(&strip_positions/1) |> List.to_tuple()
  end

  defp strip_positions(other), do: other
end
