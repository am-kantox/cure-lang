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
