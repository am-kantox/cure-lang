defmodule Cure.Types.GuardRefinementTest do
  use ExUnit.Case, async: false

  alias Cure.Types.{GuardRefinement, Refinement, Env}

  # -- AST Helpers -------------------------------------------------------------

  defp var(name), do: {:variable, [scope: :local], name}
  defp int(n), do: {:literal, [subtype: :integer], n}

  defp binop(op, left, right) do
    cat =
      cond do
        op in [:+, :-, :*, :/, :%] -> :arithmetic
        op in [:==, :!=, :<, :>, :<=, :>=] -> :comparison
        op in [:and, :or] -> :boolean
        true -> :other
      end

    {:binary_op, [operator: op, category: cat], [left, right]}
  end

  # ============================================================================
  # Constraint Extraction
  # ============================================================================

  describe "extract_constraints" do
    test "nil guard returns empty map" do
      assert GuardRefinement.extract_constraints(nil) == %{}
    end

    test "simple comparison extracts variable" do
      # x > 0
      guard = binop(:>, var("x"), int(0))
      constraints = GuardRefinement.extract_constraints(guard)
      assert Map.has_key?(constraints, "x")
      assert constraints["x"] == guard
    end

    test "compound guard extracts all variables" do
      # x > 0 and y < 100
      guard = binop(:and, binop(:>, var("x"), int(0)), binop(:<, var("y"), int(100)))
      constraints = GuardRefinement.extract_constraints(guard)
      assert Map.has_key?(constraints, "x")
      assert Map.has_key?(constraints, "y")
    end

    test "guard with single variable" do
      # x != 0
      guard = binop(:!=, var("x"), int(0))
      constraints = GuardRefinement.extract_constraints(guard)
      assert map_size(constraints) == 1
      assert Map.has_key?(constraints, "x")
    end
  end

  # ============================================================================
  # Environment Refinement
  # ============================================================================

  describe "refine_env" do
    test "nil guard leaves env unchanged" do
      env = Env.new() |> Env.push_scope() |> Env.extend("x", :int)
      refined = GuardRefinement.refine_env(env, nil, [{"x", :int}])
      assert {:ok, :int} = Env.lookup(refined, "x")
    end

    test "guard refines parameter type to refinement type" do
      env = Env.new() |> Env.push_scope() |> Env.extend("x", :int)
      guard = binop(:>, var("x"), int(0))
      refined = GuardRefinement.refine_env(env, guard, [{"x", :int}])

      {:ok, type} = Env.lookup(refined, "x")
      assert Refinement.refinement?(type)
      assert Refinement.base_type(type) == :int
      assert Refinement.var_name(type) == "x"
    end

    test "guard only refines mentioned parameters" do
      env =
        Env.new()
        |> Env.push_scope()
        |> Env.extend("x", :int)
        |> Env.extend("y", :string)

      guard = binop(:>, var("x"), int(0))
      refined = GuardRefinement.refine_env(env, guard, [{"x", :int}, {"y", :string}])

      {:ok, x_type} = Env.lookup(refined, "x")
      {:ok, y_type} = Env.lookup(refined, "y")

      # x should be refined
      assert Refinement.refinement?(x_type)
      # y should NOT be refined (not in guard)
      assert y_type == :string
    end
  end

  # ============================================================================
  # Guard Coverage Analysis
  # ============================================================================

  describe "guard coverage" do
    @tag :z3
    test "exhaustive guards: x > 0, x < 0, x == 0" do
      guards = [
        binop(:>, var("x"), int(0)),
        binop(:<, var("x"), int(0)),
        binop(:==, var("x"), int(0))
      ]

      assert GuardRefinement.check_guard_coverage(guards, "x", :int) == :exhaustive
    end

    @tag :z3
    test "non-exhaustive guards: x > 0, x < 0 (missing x == 0)" do
      guards = [
        binop(:>, var("x"), int(0)),
        binop(:<, var("x"), int(0))
      ]

      result = GuardRefinement.check_guard_coverage(guards, "x", :int)
      assert {:non_exhaustive, _} = result
    end

    test "clause without guard makes coverage exhaustive" do
      guards = [
        binop(:>, var("x"), int(0)),
        nil
      ]

      assert GuardRefinement.check_guard_coverage(guards, "x", :int) == :exhaustive
    end

    test "all nil guards is exhaustive" do
      assert GuardRefinement.check_guard_coverage([nil, nil], "x", :int) == :exhaustive
    end

    @tag :z3
    test "single guard x >= 0 is non-exhaustive" do
      guards = [binop(:>=, var("x"), int(0))]
      result = GuardRefinement.check_guard_coverage(guards, "x", :int)
      assert {:non_exhaustive, _} = result
    end

    @tag :z3
    test "x >= 0, x < 0 is exhaustive" do
      guards = [
        binop(:>=, var("x"), int(0)),
        binop(:<, var("x"), int(0))
      ]

      assert GuardRefinement.check_guard_coverage(guards, "x", :int) == :exhaustive
    end
  end

  # ============================================================================
  # Unreachable Clause Detection
  # ============================================================================

  describe "unreachable clause detection" do
    @tag :z3
    test "no unreachable clauses in disjoint guards" do
      guards = [
        binop(:>, var("x"), int(0)),
        binop(:<, var("x"), int(0)),
        binop(:==, var("x"), int(0))
      ]

      unreachable = GuardRefinement.find_unreachable_clauses(guards, "x", :int)
      assert unreachable == []
    end

    @tag :z3
    test "detect unreachable clause when previous guards cover it" do
      guards = [
        binop(:>=, var("x"), int(0)),
        binop(:<, var("x"), int(0)),
        # This clause is unreachable: x > 0 is already covered by x >= 0
        binop(:>, var("x"), int(0))
      ]

      unreachable = GuardRefinement.find_unreachable_clauses(guards, "x", :int)
      assert 2 in unreachable
    end

    test "nil guards are never unreachable" do
      guards = [
        binop(:>, var("x"), int(0)),
        nil
      ]

      unreachable = GuardRefinement.find_unreachable_clauses(guards, "x", :int)
      assert unreachable == []
    end
  end

  # ============================================================================
  # End-to-end: compilation with guards
  # ============================================================================

  describe "end-to-end guard compilation" do
    test "multi-clause function with guards compiles and runs" do
      source = """
      mod GuardTest
        fn classify(x: Int) -> String
          | x when x > 0 -> "positive"
          | x when x < 0 -> "negative"
          | _ -> "zero"
      """

      {:ok, m} = Cure.Compiler.compile_and_load(source)
      assert m.classify(5) == "positive"
      assert m.classify(-3) == "negative"
      assert m.classify(0) == "zero"
    after
      :code.purge(:guardtest)
      :code.delete(:guardtest)
    end

    test "single function with guard compiles" do
      source = """
      mod GuardSingle
        fn positive(x: Int) -> Int when x > 0 = x * 2
      """

      {:ok, m} = Cure.Compiler.compile_and_load(source)
      assert m.positive(5) == 10
    after
      :code.purge(:guardsingle)
      :code.delete(:guardsingle)
    end

    test "function with compound guard" do
      source = """
      mod GuardCompound
        fn clamp_positive(x: Int) -> Int when x > 0 and x < 100 = x
      """

      {:ok, m} = Cure.Compiler.compile_and_load(source)
      assert m.clamp_positive(50) == 50
    after
      :code.purge(:guardcompound)
      :code.delete(:guardcompound)
    end
  end
end
