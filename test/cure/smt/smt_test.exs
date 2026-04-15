defmodule Cure.SMT.SmtTest do
  use ExUnit.Case, async: false

  alias Cure.SMT.{Process, Translator, Solver}
  alias Cure.Types.Refinement

  # Helper: build MetaAST nodes for predicates
  defp var(name), do: {:variable, [scope: :local], name}
  defp int(n), do: {:literal, [subtype: :integer], n}

  defp binop(op, left, right) do
    {:binary_op, [operator: op, category: infer_category(op)], [left, right]}
  end

  defp infer_category(op) when op in [:+, :-, :*, :/, :%], do: :arithmetic
  defp infer_category(op) when op in [:==, :!=, :<, :>, :<=, :>=], do: :comparison
  defp infer_category(op) when op in [:and, :or], do: :boolean
  defp infer_category(_), do: :other

  # ============================================================================
  # SMT Process
  # ============================================================================

  describe "Cure.SMT.Process" do
    @tag :z3
    test "start and stop" do
      {:ok, pid} = Process.start_link()
      assert is_pid(pid)
      assert :ok = Process.stop(pid)
    end

    @tag :z3
    test "z3_available?" do
      assert Process.z3_available?() == true
    end

    @tag :z3
    test "simple sat query" do
      {:ok, pid} = Process.start_link()

      result =
        Process.query(pid, """
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (> x 0))
        (check-sat)
        """)

      assert {:sat, _} = result
      Process.stop(pid)
    end

    @tag :z3
    test "simple unsat query" do
      {:ok, pid} = Process.start_link()

      result =
        Process.query(pid, """
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (> x 0))
        (assert (< x 0))
        (check-sat)
        """)

      assert {:unsat, _} = result
      Process.stop(pid)
    end

    @tag :z3
    test "multiple queries on same process" do
      {:ok, pid} = Process.start_link()

      {:sat, _} = Process.query(pid, "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 5))\n(check-sat)\n")

      {:unsat, _} =
        Process.query(
          pid,
          "(reset)\n(set-logic QF_LIA)\n(declare-const x Int)\n(assert (and (> x 0) (< x 0)))\n(check-sat)\n"
        )

      Process.stop(pid)
    end
  end

  # ============================================================================
  # SMT Translator
  # ============================================================================

  describe "Cure.SMT.Translator" do
    test "translate simple comparison" do
      # x > 0
      ast = binop(:>, var("x"), int(0))
      assert Translator.translate(ast) == "(> x 0)"
    end

    test "translate arithmetic" do
      # x + y
      ast = binop(:+, var("x"), var("y"))
      assert Translator.translate(ast) == "(+ x y)"
    end

    test "translate nested expression" do
      # x + 1 > 0
      ast = binop(:>, binop(:+, var("x"), int(1)), int(0))
      assert Translator.translate(ast) == "(> (+ x 1) 0)"
    end

    test "translate boolean connective" do
      # x > 0 and x < 100
      ast = binop(:and, binop(:>, var("x"), int(0)), binop(:<, var("x"), int(100)))
      assert Translator.translate(ast) == "(and (> x 0) (< x 100))"
    end

    test "translate != operator" do
      # x != 0
      ast = binop(:!=, var("x"), int(0))
      assert Translator.translate(ast) == "(distinct x 0)"
    end

    test "collect variables" do
      # x > y + z
      ast = binop(:>, var("x"), binop(:+, var("y"), var("z")))
      assert Translator.collect_variables(ast) == ["x", "y", "z"]
    end

    test "generate complete query" do
      # x > 0
      ast = binop(:>, var("x"), int(0))
      query = Translator.generate_query(ast)
      assert String.contains?(query, "declare-const x Int")
      assert String.contains?(query, "(assert (> x 0))")
      assert String.contains?(query, "(check-sat)")
    end

    test "generate subtype query" do
      # P1: x > 0,  P2: x != 0
      pred1 = binop(:>, var("x"), int(0))
      pred2 = binop(:!=, var("x"), int(0))
      query = Translator.generate_subtype_query(pred1, pred2, "x", :int)
      assert String.contains?(query, "declare-const x Int")
      # Should assert P1 and not P2 (negation of implication)
      assert String.contains?(query, "(assert (and (> x 0) (not (distinct x 0))))")
    end
  end

  # ============================================================================
  # SMT Solver (high-level API)
  # ============================================================================

  describe "Cure.SMT.Solver" do
    @tag :z3
    test "check_sat: satisfiable constraint" do
      # x > 0 is satisfiable
      ast = binop(:>, var("x"), int(0))
      assert Solver.check_sat(ast) == :sat
    end

    @tag :z3
    test "check_sat: unsatisfiable constraint" do
      # x > 0 and x < 0 is unsatisfiable
      ast = binop(:and, binop(:>, var("x"), int(0)), binop(:<, var("x"), int(0)))
      assert Solver.check_sat(ast) == :unsat
    end

    @tag :z3
    test "prove_implication: x > 0 => x != 0" do
      pred1 = binop(:>, var("x"), int(0))
      pred2 = binop(:!=, var("x"), int(0))
      assert Solver.prove_implication(pred1, pred2, "x", :int) == true
    end

    @tag :z3
    test "prove_implication: x > 0 does NOT imply x > 5" do
      pred1 = binop(:>, var("x"), int(0))
      pred2 = binop(:>, var("x"), int(5))
      assert Solver.prove_implication(pred1, pred2, "x", :int) == false
    end

    @tag :z3
    test "prove_implication: 0 <= x <= 100 => x >= 0" do
      pred1 = binop(:and, binop(:>=, var("x"), int(0)), binop(:<=, var("x"), int(100)))
      pred2 = binop(:>=, var("x"), int(0))
      assert Solver.prove_implication(pred1, pred2, "x", :int) == true
    end

    @tag :z3
    test "is_satisfiable?: x > 0 has solutions" do
      pred = binop(:>, var("x"), int(0))
      assert Solver.is_satisfiable?(pred, "x", :int) == true
    end

    @tag :z3
    test "is_satisfiable?: x > 0 and x < 0 has no solutions" do
      pred = binop(:and, binop(:>, var("x"), int(0)), binop(:<, var("x"), int(0)))
      assert Solver.is_satisfiable?(pred, "x", :int) == false
    end
  end

  # ============================================================================
  # Refinement Types
  # ============================================================================

  describe "Cure.Types.Refinement" do
    test "new and accessors" do
      pred = binop(:>, var("x"), int(0))
      r = Refinement.new(:int, "x", pred)

      assert Refinement.refinement?(r)
      assert Refinement.base_type(r) == :int
      assert Refinement.var_name(r) == "x"
      assert Refinement.predicate(r) == pred
    end

    test "refinement? returns false for non-refinement" do
      refute Refinement.refinement?(:int)
      refute Refinement.refinement?({:list, :int})
    end

    @tag :z3
    test "subtype?: Positive <: NonZero" do
      # {x: Int | x > 0} <: {x: Int | x != 0}
      positive = Refinement.new(:int, "x", binop(:>, var("x"), int(0)))
      nonzero = Refinement.new(:int, "x", binop(:!=, var("x"), int(0)))
      assert Refinement.subtype?(positive, nonzero) == true
    end

    @tag :z3
    test "subtype?: Percentage <: NonNegative" do
      # {x: Int | 0 <= x and x <= 100} <: {x: Int | x >= 0}
      pct = Refinement.new(:int, "x", binop(:and, binop(:>=, var("x"), int(0)), binop(:<=, var("x"), int(100))))
      non_neg = Refinement.new(:int, "x", binop(:>=, var("x"), int(0)))
      assert Refinement.subtype?(pct, non_neg) == true
    end

    @tag :z3
    test "subtype?: NonZero is NOT subtype of Positive" do
      # {x: Int | x != 0} is NOT <: {x: Int | x > 0} (x could be -1)
      nonzero = Refinement.new(:int, "x", binop(:!=, var("x"), int(0)))
      positive = Refinement.new(:int, "x", binop(:>, var("x"), int(0)))
      assert Refinement.subtype?(nonzero, positive) == false
    end

    test "subtype?: refinement is subtype of its base" do
      positive = Refinement.new(:int, "x", binop(:>, var("x"), int(0)))
      assert Refinement.subtype?(positive, :int) == true
    end

    @tag :z3
    test "satisfiable?: x > 0 is satisfiable" do
      r = Refinement.new(:int, "x", binop(:>, var("x"), int(0)))
      assert Refinement.satisfiable?(r) == true
    end

    @tag :z3
    test "satisfiable?: x > 0 and x < 0 is NOT satisfiable" do
      r = Refinement.new(:int, "x", binop(:and, binop(:>, var("x"), int(0)), binop(:<, var("x"), int(0))))
      assert Refinement.satisfiable?(r) == false
    end
  end

  # ============================================================================
  # Type System Integration
  # ============================================================================

  describe "Type.subtype? with refinements" do
    alias Cure.Types.Type

    @tag :z3
    test "refinement subtype of base type" do
      positive = Refinement.new(:int, "x", binop(:>, var("x"), int(0)))
      assert Type.subtype?(positive, :int) == true
    end

    @tag :z3
    test "refinement subtype of compatible refinement" do
      positive = Refinement.new(:int, "x", binop(:>, var("x"), int(0)))
      nonzero = Refinement.new(:int, "x", binop(:!=, var("x"), int(0)))
      assert Type.subtype?(positive, nonzero) == true
    end
  end

  # ============================================================================
  # SMT Translator Fallback
  # ============================================================================

  describe "Translator fallback" do
    test "unrecognized AST produces SMT comment with true" do
      result = Translator.translate({:weird_node, [line: 1], :stuff})
      assert result =~ "untranslatable"
      assert result =~ "true"
    end

    test "conditional translates to ite" do
      cond_ast = {:conditional, [], [binop(:>, var("x"), int(0)), int(1), int(0)]}
      result = Translator.translate(cond_ast)
      assert result =~ "ite"
      assert result =~ "(> x 0)"
    end
  end
end
