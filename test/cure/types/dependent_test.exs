defmodule Cure.Types.DependentTest do
  use ExUnit.Case, async: false

  alias Cure.Types.Dependent
  alias Cure.SMT.Solver

  # -- AST helpers
  defp var(n), do: {:variable, [scope: :local], n}
  defp int(n), do: {:literal, [subtype: :integer], n}
  defp binop(op, l, r), do: {:binary_op, [operator: op, category: :comparison], [l, r]}

  describe "Dependent type representation" do
    test "create and query dependent type" do
      dt = Dependent.new("Vector", ["T"], [{"n", :int}])
      assert Dependent.dependent?(dt)
      assert Dependent.value_param_names(dt) == ["n"]
    end

    test "create with constraints" do
      constraint = binop(:>, var("n"), int(0))
      dt = Dependent.new("Vector", ["T"], [{"n", :int}], [constraint])
      vcs = Dependent.generate_vc(dt, [])
      assert length(vcs) == 1
    end

    test "compatible? checks same constructor" do
      dt1 = Dependent.new("Vector", ["T"], [{"n", :int}])
      dt2 = Dependent.new("Vector", ["U"], [{"m", :int}])
      dt3 = Dependent.new("List", ["T"], [])
      assert Dependent.compatible?(dt1, dt2)
      refute Dependent.compatible?(dt1, dt3)
    end

    test "substitute replaces value params in constraints" do
      constraint = binop(:>, var("n"), int(0))
      dt = Dependent.new("Vector", ["T"], [{"n", :int}], [constraint])

      substituted = Dependent.substitute(dt, %{"n" => int(5)})
      {:dependent, _, _, _, [new_constraint]} = substituted

      # The constraint should now have 5 instead of n
      {:binary_op, _, [left, _right]} = new_constraint
      assert {:literal, _, 5} = left
    end
  end

  describe "SMT counterexample extraction" do
    @tag :z3
    test "prove_with_counterexample: proven case" do
      pred1 = binop(:>, var("x"), int(0))
      pred2 = binop(:!=, var("x"), int(0))
      assert {:proven, nil} = Solver.prove_with_counterexample(pred1, pred2, "x", :int)
    end

    @tag :z3
    test "prove_with_counterexample: failed with model" do
      pred1 = binop(:!=, var("x"), int(0))
      pred2 = binop(:>, var("x"), int(0))
      result = Solver.prove_with_counterexample(pred1, pred2, "x", :int)
      assert {:failed, model} = result
      assert is_map(model)
    end
  end

  describe "Type checker: constrained function signatures" do
    test "function with guard registers constrained type" do
      source = """
      mod ConstrainedTest
        fn positive(x: Int) -> Int when x > 0 = x * 2
        fn use_it() -> Int = positive(5)
      """

      # Should compile without errors (5 > 0 is satisfiable)
      assert {:ok, _} = Cure.Compiler.compile_and_load(source, check_types: true)
    after
      :code.purge(:"Cure.ConstrainedTest")
      :code.delete(:"Cure.ConstrainedTest")
    end

    test "function with guard compiles and runs" do
      source = """
      mod GuardedFn
        fn safe_div(a: Int, b: Int) -> Int when b != 0 = a / b
        fn main() -> Int = safe_div(42, 7)
      """

      {:ok, m} = Cure.Compiler.compile_and_load(source)
      assert m.main() == 6
    after
      :code.purge(:"Cure.GuardedFn")
      :code.delete(:"Cure.GuardedFn")
    end
  end

  describe "generate_vc with argument substitution" do
    test "substitutes arguments into constraints" do
      constraint = binop(:>, var("n"), int(0))
      dt = Dependent.new("Vector", ["T"], [{"n", :int}], [constraint])

      # Simulate calling with argument 5
      vcs = Dependent.generate_vc(dt, [int(5)])
      assert [vc] = vcs

      # The constraint should now have 5 instead of n
      {:binary_op, _, [left, _right]} = vc
      assert {:literal, _, 5} = left
    end

    test "no constraints returns empty VCs" do
      dt = Dependent.new("Vector", ["T"], [{"n", :int}])
      assert [] = Dependent.generate_vc(dt, [int(3)])
    end

    test "multiple constraints are all substituted" do
      c1 = binop(:>, var("n"), int(0))
      c2 = binop(:<, var("n"), int(100))
      dt = Dependent.new("Vector", ["T"], [{"n", :int}], [c1, c2])

      vcs = Dependent.generate_vc(dt, [int(42)])
      assert [_, _] = vcs
    end
  end

  describe "compatible? with constraints" do
    test "same constraints are compatible" do
      c = binop(:>, var("n"), int(0))
      dt1 = Dependent.new("V", ["T"], [{"n", :int}], [c])
      dt2 = Dependent.new("V", ["T"], [{"m", :int}], [c])
      assert Dependent.compatible?(dt1, dt2)
    end

    test "different constraints are incompatible" do
      c1 = binop(:>, var("n"), int(0))
      c2 = binop(:>, var("n"), int(10))
      dt1 = Dependent.new("V", ["T"], [{"n", :int}], [c1])
      dt2 = Dependent.new("V", ["T"], [{"m", :int}], [c2])
      refute Dependent.compatible?(dt1, dt2)
    end

    test "empty constraints on one side are compatible" do
      c = binop(:>, var("n"), int(0))
      dt1 = Dependent.new("V", ["T"], [{"n", :int}])
      dt2 = Dependent.new("V", ["T"], [{"m", :int}], [c])
      assert Dependent.compatible?(dt1, dt2)
    end
  end

  describe "Std.Vector" do
    setup do
      # Load all stdlib dependencies first
      for name <- ~w(core list pair math string io) do
        path = Path.join(["lib", "std", "#{name}.cure"])

        if File.exists?(path) do
          Cure.Compiler.compile_and_load(File.read!(path), file: path)
        end
      end

      case Cure.Compiler.compile_and_load(
             File.read!("lib/std/vector.cure"),
             file: "lib/std/vector.cure"
           ) do
        {:ok, _} -> :ok
        {:error, _} -> :ok
      end

      :ok
    end

    test "empty vector" do
      m = :"Cure.Std.Vector"
      vec = m.empty()
      assert m.length(vec) == 0
      assert m.is_empty(vec) == true
    end

    test "singleton" do
      m = :"Cure.Std.Vector"
      vec = m.singleton(42)
      assert m.length(vec) == 1
      assert m.head(vec) == 42
    end

    test "cons increases length" do
      m = :"Cure.Std.Vector"
      v0 = m.empty()
      v1 = m.cons(1, v0)
      v2 = m.cons(2, v1)
      assert m.length(v2) == 2
    end

    test "append combines vectors" do
      m = :"Cure.Std.Vector"
      a = m.from_list([1, 2])
      b = m.from_list([3, 4])
      c = m.append(a, b)
      assert m.length(c) == 4
      assert m.to_list(c) == [1, 2, 3, 4]
    end

    test "map preserves length" do
      m = :"Cure.Std.Vector"
      v = m.from_list([1, 2, 3])
      doubled = m.map(v, fn x -> x * 2 end)
      assert m.length(doubled) == 3
      assert m.to_list(doubled) == [2, 4, 6]
    end
  end
end
