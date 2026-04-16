defmodule Cure.Types.SigmaTest do
  use ExUnit.Case, async: true

  alias Cure.Types.{Sigma, Type}

  defp var(n), do: {:variable, [scope: :local], n}
  defp int(n), do: {:literal, [subtype: :integer], n}

  describe "construction" do
    test "new/3 builds a sigma" do
      s = Sigma.new("n", :int, var("Vector(T,n)"))
      assert Sigma.sigma?(s)
      assert Sigma.var(s) == "n"
      assert Sigma.fst(s) == :int
    end

    test "non-sigma is rejected by sigma?/1" do
      refute Sigma.sigma?({:list, :int})
      refute Sigma.sigma?(:any)
      refute Sigma.sigma?(nil)
    end
  end

  describe "from_function_call/2" do
    test "Sigma(Int, Int) -- non-dependent" do
      meta = [name: "Sigma"]
      args = [var("Int"), var("Int")]
      s = Sigma.from_function_call(meta, args)
      assert {:sigma, "_", :int, _} = s
    end

    test "Sigma(n: Nat, ...) -- dependent" do
      meta = [name: "Sigma"]
      args = [{:param, [type: var("Nat")], "n"}, var("Int")]
      s = Sigma.from_function_call(meta, args)
      assert {:sigma, "n", :int, _} = s
    end

    test "DPair is also recognised" do
      meta = [name: "DPair"]
      args = [var("Int"), var("Int")]
      assert {:sigma, "_", :int, _} = Sigma.from_function_call(meta, args)
    end

    test "non-sigma name returns :not_sigma" do
      assert :not_sigma = Sigma.from_function_call([name: "List"], [var("Int")])
    end

    test "wrong arity returns :not_sigma" do
      assert :not_sigma = Sigma.from_function_call([name: "Sigma"], [])
    end
  end

  describe "subtyping" do
    test "two sigma types subtype componentwise" do
      s1 = Sigma.new("_", :int, var("Int"))
      s2 = Sigma.new("_", :int, var("Int"))
      assert Sigma.subtype?(s1, s2)
    end

    test "sigma <: tuple forgets dependency" do
      s = Sigma.new("n", :int, var("Int"))
      assert Sigma.subtype?(s, {:tuple, [:int, :int]})
    end

    test "tuple <: sigma when components match" do
      s = Sigma.new("n", :int, var("Int"))
      assert Sigma.subtype?({:tuple, [:int, :int]}, s)
    end

    test "fails on incompatible first component" do
      s1 = Sigma.new("_", :int, var("Int"))
      s2 = Sigma.new("_", :string, var("Int"))
      refute Sigma.subtype?(s1, s2)
    end
  end

  describe "instantiate/2" do
    test "substitutes the bound variable" do
      # Sigma(n: Int, n)  instantiated at 5  ->  resolves the second to Int
      s = Sigma.new("n", :int, var("Int"))
      assert :int = Sigma.instantiate(s, int(5))
    end
  end

  describe "Type.resolve/1 integration" do
    test "Sigma(...) parser shape becomes a sigma type" do
      ast = {:function_call, [name: "Sigma"], [var("Int"), var("Int")]}
      assert {:sigma, "_", :int, _} = Type.resolve(ast)
    end

    test "Sigma(name: T1, T2) becomes a dependent sigma" do
      ast =
        {:function_call, [name: "Sigma"], [{:param, [type: var("Nat")], "n"}, var("Int")]}

      assert {:sigma, "n", :int, _} = Type.resolve(ast)
    end
  end
end
