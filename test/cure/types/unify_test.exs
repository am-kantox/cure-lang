defmodule Cure.Types.UnifyTest do
  use ExUnit.Case, async: true

  alias Cure.Types.Unify

  describe "atomic types" do
    test "matches identical atoms" do
      assert {:ok, %{}, _} = Unify.unify(:int, :int)
    end

    test "fails on incompatible atoms" do
      assert {:error, _, _} = Unify.unify(:int, :string)
    end

    test "Int unifies with Float (widening)" do
      assert {:ok, _, _} = Unify.unify(:int, :float)
    end

    test ":any matches anything" do
      assert {:ok, _, _} = Unify.unify(:any, :int)
      assert {:ok, _, _} = Unify.unify(:string, :any)
    end
  end

  describe "type variables" do
    test "binds a fresh variable" do
      assert {:ok, %{"T" => :int}, _} = Unify.unify({:type_var, "T"}, :int)
    end

    test "two distinct vars unify by binding one to the other" do
      assert {:ok, %{"T" => {:type_var, "U"}}, _} =
               Unify.unify({:type_var, "T"}, {:type_var, "U"})
    end

    test "consistent re-unification is fine" do
      {:ok, s, _} = Unify.unify({:type_var, "T"}, :int)
      assert {:ok, _, _} = Unify.unify({:type_var, "T"}, :int, s)
    end

    test "inconsistent re-unification fails" do
      {:ok, s, _} = Unify.unify({:type_var, "T"}, :int)
      assert {:error, _, _} = Unify.unify({:type_var, "T"}, :string, s)
    end
  end

  describe "composites" do
    test "lists" do
      assert {:ok, %{"T" => :int}, _} =
               Unify.unify({:list, {:type_var, "T"}}, {:list, :int})
    end

    test "tuples" do
      assert {:ok, %{"A" => :int, "B" => :string}, _} =
               Unify.unify(
                 {:tuple, [{:type_var, "A"}, {:type_var, "B"}]},
                 {:tuple, [:int, :string]}
               )
    end

    test "function types: contravariance not required for unify" do
      assert {:ok, %{"T" => :int}, _} =
               Unify.unify({:fun, [{:type_var, "T"}], :string}, {:fun, [:int], :string})
    end

    test "ADT same head, different args" do
      assert {:ok, %{"T" => :int}, _} =
               Unify.unify(
                 {:adt, :option, [{:type_var, "T"}]},
                 {:adt, :option, [:int]}
               )
    end

    test "ADT different head fails" do
      assert {:error, _, _} =
               Unify.unify({:adt, :option, [:int]}, {:adt, :result, [:int]})
    end

    test "maps unify keys and values" do
      assert {:ok, %{"K" => :atom, "V" => :int}, _} =
               Unify.unify(
                 {:map, {:type_var, "K"}, {:type_var, "V"}},
                 {:map, :atom, :int}
               )
    end

    test "named types match by name" do
      assert {:ok, _, _} = Unify.unify({:named, "Point"}, {:named, "Point"})
    end

    test "named type matches a resolved record of the same name" do
      rec = {:record, :point, %{"x" => :int, "y" => :int}}
      assert {:ok, _, _} = Unify.unify({:named, "Point"}, rec)
      assert {:ok, _, _} = Unify.unify(rec, {:named, "Point"})
    end

    test "named type matches a resolved ADT of the same name" do
      adt = {:adt, :point, [:int, :int]}
      assert {:ok, _, _} = Unify.unify({:named, "Point"}, adt)
      assert {:ok, _, _} = Unify.unify(adt, {:named, "Point"})
    end

    test "refinements are transparent to unification" do
      refined = {:refinement, :int, "x", nil}

      assert {:ok, %{"T" => :int}, _} =
               Unify.unify({:type_var, "T"}, refined)

      assert {:ok, %{"T" => :int}, _} =
               Unify.unify(refined, {:type_var, "T"})
    end
  end

  describe "occurs check" do
    test "rejects T = List(T)" do
      assert {:error, _, _} =
               Unify.unify({:type_var, "T"}, {:list, {:type_var, "T"}})
    end
  end

  describe "apply_subst/2" do
    test "substitutes through a list" do
      subst = %{"T" => :int}

      assert {:list, :int} = Unify.apply_subst({:list, {:type_var, "T"}}, subst)
    end

    test "substitutes through nested types" do
      subst = %{"A" => :int, "B" => :string}

      assert {:fun, [:int], :string} =
               Unify.apply_subst({:fun, [{:type_var, "A"}], {:type_var, "B"}}, subst)
    end

    test "leaves unbound vars alone" do
      assert {:type_var, "X"} = Unify.apply_subst({:type_var, "X"}, %{})
    end

    test "substitutes through maps" do
      subst = %{"K" => :atom, "V" => :int}

      assert {:map, :atom, :int} =
               Unify.apply_subst({:map, {:type_var, "K"}, {:type_var, "V"}}, subst)
    end

    test "substitutes through refinements" do
      subst = %{"T" => :int}

      assert {:refinement, :int, "x", nil} =
               Unify.apply_subst({:refinement, {:type_var, "T"}, "x", nil}, subst)
    end

    test "substitutes through effect-annotated function types" do
      subst = %{"A" => :int, "B" => :string}
      effs = MapSet.new([:io])

      assert {:effun, [:int], :string, ^effs} =
               Unify.apply_subst(
                 {:effun, [{:type_var, "A"}], {:type_var, "B"}, effs},
                 subst
               )
    end
  end

  describe "unify_many/1" do
    test "all consistent" do
      cs = [{{:type_var, "T"}, :int}, {{:list, {:type_var, "T"}}, {:list, :int}}]
      assert {:ok, %{"T" => :int}, _} = Unify.unify_many(cs)
    end

    test "stops at the first failure" do
      cs = [{{:type_var, "T"}, :int}, {{:type_var, "T"}, :string}]
      assert {:error, _, _} = Unify.unify_many(cs)
    end
  end
end
