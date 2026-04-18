defmodule Cure.Types.PatternRefinementNarrowingTest do
  use ExUnit.Case, async: true

  alias Cure.Types.PatternRefinement

  # -- Simple patterns -------------------------------------------------------

  describe "variable and wildcard patterns" do
    test "bare variable binds to scrutinee type" do
      pat = {:variable, [], "x"}
      assert {%{"x" => :int}, :int} = PatternRefinement.narrow(pat, :int)
    end

    test "wildcard produces no bindings" do
      pat = {:variable, [], "_"}
      assert {%{}, :int} = PatternRefinement.narrow(pat, :int)
    end

    test "_prefixed variable produces no binding" do
      pat = {:variable, [], "_unused"}
      assert {%{}, :int} = PatternRefinement.narrow(pat, :int)
    end

    test "pin operator contributes no new binding" do
      pat = {:pin, [], [{:variable, [], "x"}]}
      assert {%{}, :int} = PatternRefinement.narrow(pat, :int)
    end
  end

  # -- Literal-equality witnesses -------------------------------------------

  describe "literal patterns narrow scrutinee to equality refinement" do
    test "integer literal 0 against :int" do
      pat = {:literal, [subtype: :integer], 0}
      {bindings, narrowed} = PatternRefinement.narrow(pat, :int)
      assert bindings == %{}
      assert match?({:refinement, :int, "__value__", _pred}, narrowed)
    end

    test "atom literal :ok against :atom" do
      pat = {:literal, [subtype: :symbol], :ok}
      {bindings, narrowed} = PatternRefinement.narrow(pat, :atom)
      assert bindings == %{}
      assert match?({:refinement, :atom, "__value__", _pred}, narrowed)
    end

    test "unknown base leaves scrutinee unchanged" do
      pat = {:literal, [subtype: :unknown], "raw"}
      {bindings, narrowed} = PatternRefinement.narrow(pat, {:named, "Foo"})
      assert bindings == %{}
      assert narrowed == {:named, "Foo"}
    end
  end

  # -- Tuple patterns --------------------------------------------------------

  describe "tuple patterns" do
    test "tuple with matching arity zips element types" do
      pat = {:tuple, [], [{:variable, [], "a"}, {:variable, [], "b"}]}
      scrutinee = {:tuple, [:int, :string]}

      {bindings, narrowed} = PatternRefinement.narrow(pat, scrutinee)
      assert bindings == %{"a" => :int, "b" => :string}
      assert narrowed == {:tuple, [:int, :string]}
    end

    test "tuple with literal element narrows that slot" do
      pat =
        {:tuple, [],
         [
           {:literal, [subtype: :integer], 0},
           {:variable, [], "snd"}
         ]}

      scrutinee = {:tuple, [:int, :string]}

      {bindings, {:tuple, [t0, t1]}} = PatternRefinement.narrow(pat, scrutinee)
      assert bindings == %{"snd" => :string}
      assert match?({:refinement, :int, "__value__", _}, t0)
      assert t1 == :string
    end
  end

  # -- List patterns ---------------------------------------------------------

  describe "list patterns" do
    test "cons pattern binds head and tail" do
      pat = {:list, [cons: true], [{:variable, [], "h"}, {:variable, [], "t"}]}
      scrutinee = {:list, :int}

      {bindings, narrowed} = PatternRefinement.narrow(pat, scrutinee)
      assert bindings == %{"h" => :int, "t" => {:list, :int}}
      assert narrowed == {:list, :int}
    end

    test "fixed list binds every element" do
      pat = {:list, [], [{:variable, [], "a"}, {:variable, [], "b"}]}
      scrutinee = {:list, :string}

      {bindings, narrowed} = PatternRefinement.narrow(pat, scrutinee)
      assert bindings == %{"a" => :string, "b" => :string}
      assert narrowed == {:list, :string}
    end
  end

  # -- Map patterns with disjoint-tag witnesses ------------------------------

  describe "map patterns" do
    test "map pattern with kind: :ok narrows to :variant" do
      pat =
        {:map, [],
         [
           {:pair, [],
            [
              {:literal, [subtype: :symbol], :kind},
              {:literal, [subtype: :symbol], :ok}
            ]},
           {:pair, [],
            [
              {:literal, [subtype: :symbol], :value},
              {:variable, [], "v"}
            ]}
         ]}

      {bindings, narrowed} = PatternRefinement.narrow(pat, :any)

      assert Map.has_key?(bindings, "v")
      assert narrowed == {:variant, :ok, []}
    end

    test "map pattern without :kind field leaves scrutinee unchanged" do
      pat =
        {:map, [],
         [
           {:pair, [], [{:literal, [subtype: :symbol], :a}, {:variable, [], "a"}]}
         ]}

      {_, narrowed} = PatternRefinement.narrow(pat, :any)
      assert narrowed == :any
    end
  end

  # -- Constructor patterns --------------------------------------------------

  describe "constructor patterns" do
    test "Ok(v) narrows to :variant :ok" do
      pat =
        {:function_call, [name: "Ok"],
         [
           {:variable, [], "v"}
         ]}

      {bindings, narrowed} = PatternRefinement.narrow(pat, :any)

      assert Map.has_key?(bindings, "v")
      assert narrowed == {:variant, :ok, []}
    end

    test "Error(e) narrows to :variant :error" do
      pat =
        {:function_call, [name: "Error"],
         [
           {:variable, [], "e"}
         ]}

      {_bindings, narrowed} = PatternRefinement.narrow(pat, :any)
      assert narrowed == {:variant, :error, []}
    end

    test "lowercase call (not a constructor) leaves scrutinee alone" do
      pat = {:function_call, [name: "get"], []}
      {_, narrowed} = PatternRefinement.narrow(pat, :int)
      assert narrowed == :int
    end
  end

  # -- Record patterns -------------------------------------------------------

  describe "record patterns" do
    test "Point{x, y} binds both fields" do
      pat =
        {:function_call, [name: "Point", record: true],
         [
           {:variable, [], "x"},
           {:variable, [], "y"}
         ]}

      {bindings, _narrowed} = PatternRefinement.narrow(pat, {:named, "Point"})
      assert Map.has_key?(bindings, "x")
      assert Map.has_key?(bindings, "y")
    end

    test "Point{x: 0, y: v} only binds v" do
      pat =
        {:function_call, [name: "Point", record: true],
         [
           {:pair, [],
            [
              {:literal, [subtype: :symbol], :x},
              {:literal, [subtype: :integer], 0}
            ]},
           {:pair, [],
            [
              {:literal, [subtype: :symbol], :y},
              {:variable, [], "v"}
            ]}
         ]}

      {bindings, _narrowed} = PatternRefinement.narrow(pat, {:named, "Point"})
      assert Map.has_key?(bindings, "v")
      refute Map.has_key?(bindings, "x")
    end
  end
end
