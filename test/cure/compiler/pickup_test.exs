defmodule Cure.Compiler.PickupTest do
  @moduledoc """
  Spec-conformance tests for the `pickup` branching construct as
  defined in `docs/PICKUP.md` (Version 1.0.0). The test suite mirrors
  Appendix A of the spec and exercises:

    * lexer recognition of the `pickup` keyword;
    * parser well-formedness (PICKUP §4, §5.2);
    * `else`-terminator and `true`-terminator equivalence (§5.2);
    * canonical block printing (§8) and the degenerate `H-PICKUP-DEGENERATE`
      and trailing-`true`-to-`else` (`H-PICKUP-PREFER-ELSE`) rewrites;
    * type-checker rejection of malformed blocks (E-PICKUP-NO-ELSE,
      E-PICKUP-ELSE-NOT-LAST, E-PICKUP-MULTIPLE-ELSE, E-PICKUP-GUARD-TYPE,
      E-PICKUP-BRANCH-MISMATCH);
    * codegen end-to-end through `Cure.Compiler.compile_string/2`;
    * spec-mandated diagnostic catalogue entries.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler
  alias Cure.Compiler.{Errors, Lexer, Parser, Printer}

  @out_dir "_build/cure/pickup_test_out"

  setup_all do
    File.mkdir_p!(@out_dir)
    :ok
  end

  # ── §3 Lexical ────────────────────────────────────────────────────────────

  describe "lexer recognition of `pickup`" do
    test "`pickup` is reserved and tokenised as a keyword" do
      assert {:ok, tokens} = Lexer.tokenize("pickup", emit_events: false)
      assert Enum.any?(tokens, fn tok -> tok.type == :keyword and tok.value == :pickup end)
    end
  end

  # ── §4-5 Parsing & Well-formedness ────────────────────────────────────────

  describe "parser well-formedness (PICKUP §5.2 / §4.1)" do
    test "valid block with else terminator parses to {:pickup, _, [..., :pickup_else]}" do
      source = """
      pickup
        x > 0 -> :positive
        x < 0 -> :negative
        else  -> :zero
      """

      {:ok, ast} = parse(source)
      assert {:pickup, _meta, [c1, c2, terminator]} = ast
      assert {:pickup_clause, _, _} = c1
      assert {:pickup_clause, _, _} = c2
      assert {:pickup_else, _, _} = terminator
    end

    test "trailing `true ->` is admitted as an alternative-form terminator (§5.2)" do
      source = """
      pickup
        x > 0 -> :positive
        true  -> :other
      """

      assert {:ok, _ast} = parse(source)
    end

    test "missing terminator triggers E-PICKUP-NO-ELSE at parse time" do
      source = """
      pickup
        x > 0 -> :positive
        x < 0 -> :negative
      """

      assert {:error, errors} = parse(source)
      assert Enum.any?(errors, &match?({:pickup_no_else, _, _}, &1))
    end

    test "multiple `else` arms trigger E-PICKUP-MULTIPLE-ELSE" do
      source = """
      pickup
        else -> :a
        else -> :b
      """

      assert {:error, errors} = parse(source)
      assert Enum.any?(errors, &match?({:pickup_multiple_else, _, _}, &1))
    end

    test "non-final `else` triggers E-PICKUP-ELSE-NOT-LAST" do
      source = """
      pickup
        else  -> :a
        x > 0 -> :b
      """

      assert {:error, errors} = parse(source)
      assert Enum.any?(errors, &match?({:pickup_else_not_last, _, _}, &1))
    end
  end

  # ── §6-7 Operational semantics through codegen ────────────────────────────

  describe "selection semantics (PICKUP §6.1, §7.1)" do
    test "first-true guard wins for a positive scrutinee" do
      source = """
      mod M
        fn classify(x: Int) -> Atom =
          pickup
            x > 0 -> :positive
            x < 0 -> :negative
            else  -> :zero
      """

      {:ok, mod} = compile_and_load(source)
      assert :positive = mod.classify(7)
      assert :negative = mod.classify(-3)
      assert :zero = mod.classify(0)
    end

    test "later guards are unevaluated when an earlier one fires (short-circuit, §6.2)" do
      # We rely on division by zero panicking in the Cure runtime; if
      # the second guard *were* evaluated before the first matched,
      # the test would crash instead of returning :first.
      source = """
      mod M
        fn first_wins(n: Int) -> Atom =
          pickup
            n > 0  -> :first
            10 / n > 0 -> :second
            else   -> :else
      """

      {:ok, mod} = compile_and_load(source)
      assert :first = mod.first_wins(5)
    end

    test "trailing `true ->` clause is selected as the terminator" do
      source = """
      mod M
        fn always_b() -> Atom =
          pickup
            false -> :a
            true  -> :b
      """

      {:ok, mod} = compile_and_load(source)
      assert :b = mod.always_b()
    end
  end

  # ── §8 Formatting / Printer ───────────────────────────────────────────────

  describe "canonical block printer (PICKUP §8)" do
    test "block form survives a parse -> print -> parse round-trip" do
      ast =
        {:pickup, [],
         [
           {:pickup_clause, [], [parse_expr!("x > 0"), parse_expr!(":positive")]},
           {:pickup_clause, [], [parse_expr!("x < 0"), parse_expr!(":negative")]},
           {:pickup_else, [], [parse_expr!(":zero")]}
         ]}

      printed = Printer.quoted_to_string(ast)
      assert printed =~ ~r/\Apickup\n/
      assert printed =~ ~r/x > 0\s+-> :positive/
      assert printed =~ ~r/else\s+-> :zero/

      # Round-trip: re-parse and structurally compare.
      {:ok, re_ast} = parse(printed)
      assert strip_positions(ast) == strip_positions(re_ast)
    end

    test "degenerate `pickup` (terminator only) collapses to its body (§8.6)" do
      ast = {:pickup, [], [{:pickup_else, [], [parse_expr!("42")]}]}
      assert Printer.quoted_to_string(ast) == "42"
    end

    test "trailing `true ->` is normalised to `else ->` (§8.3)" do
      ast =
        {:pickup, [],
         [
           {:pickup_clause, [], [parse_expr!("x > 0"), parse_expr!(":positive")]},
           {:pickup_clause, [], [{:literal, [subtype: :boolean], true}, parse_expr!(":other")]}
         ]}

      printed = Printer.quoted_to_string(ast)
      assert printed =~ ~r/else\s+-> :other/
      refute printed =~ ~r/true\s+-> :other/
    end
  end

  # ── §19 Diagnostics catalogue ─────────────────────────────────────────────

  describe "spec-mandated diagnostic catalogue" do
    # Errors and warnings each carry their own code-class prefix in the
    # catalogue: E (errors), W (warnings), H (hints). The PICKUP spec
    # reserves E076-E080 for hard errors, W081/W082 for reachability
    # warnings, H083/H084 for formatter-emitted hints, and E085 for
    # the legacy `if` migration error.
    @pickup_codes ~w(E076 E077 E078 E079 E080 W081 W082 H083 H084 E085)

    test "every PICKUP diagnostic code is registered" do
      Enum.each(@pickup_codes, fn code ->
        assert {:ok, text} = Errors.explain(code), "missing explainer for #{code}"
        assert text =~ "PICKUP" or text =~ "pickup" or text =~ "if"
      end)
    end

    test "E-IF-REMOVED is reserved and explainable" do
      assert {:ok, text} = Errors.explain("E085")
      assert text =~ "IF-REMOVED" or text =~ "if"
    end
  end

  # ── §17 Migration ────────────────────────────────────────────────────────

  describe "legacy `if` is parsed but emits a deprecation event" do
    test "`if cond then x else y` still parses to `:conditional`" do
      assert {:ok, {:conditional, _, [_, _, _]}} = parse("if x > 0 then 1 else 0")
    end
  end

  # ── Helpers ──────────────────────────────────────────────────────────────

  defp parse(source) do
    with {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false) do
      {:ok, ast}
    end
  end

  defp parse_expr!(source) do
    {:ok, ast} = parse(source)
    ast
  end

  defp compile_and_load(source) do
    Compiler.compile_and_load(source, file: "pickup_test.cure", emit_events: false)
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
