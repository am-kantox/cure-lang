defmodule Cure.Types.HolesTest do
  use ExUnit.Case, async: true

  alias Cure.Types.Holes

  describe "construction" do
    test "new/2 builds a hole" do
      h = Holes.new("body", %{"x" => :int})
      assert Holes.hole?(h)
      assert Holes.name(h) == "body"
      assert Holes.context(h) == %{"x" => :int}
    end

    test "hole?/1 rejects non-holes" do
      refute Holes.hole?({:int, []})
      refute Holes.hole?(:any)
    end
  end

  describe "recognise/1" do
    test "?body in variable position" do
      assert {:hole, "body"} = Holes.recognise({:variable, [], "?body"})
    end

    test "?? as anonymous" do
      assert {:hole, :anon} = Holes.recognise({:variable, [], "??"})
    end

    test "underscore as legacy hole" do
      assert {:hole, "_"} = Holes.recognise({:variable, [], "_"})
    end

    test "non-hole returns :not_a_hole" do
      assert :not_a_hole = Holes.recognise({:variable, [], "x"})
      assert :not_a_hole = Holes.recognise({:literal, [], 42})
    end

    test "function-call shape with ? prefix" do
      assert {:hole, "x"} = Holes.recognise({:function_call, [name: "?x"], []})
    end
  end

  describe "render/3" do
    test "formats a goal with empty context" do
      out = Holes.render("?body", :int, %{})
      assert out =~ "?body : Int"
      assert out =~ "(empty)"
    end

    test "formats a goal with multiple bindings" do
      out = Holes.render("?body", :string, %{"x" => :int, "y" => :bool})
      assert out =~ "?body : String"
      assert out =~ "x : Int"
      assert out =~ "y : Bool"
    end
  end

  describe "number_anonymous/1" do
    test "numbers ?? in source order" do
      ast =
        {:tuple, [],
         [
           {:variable, [], "??"},
           {:literal, [], 1},
           {:variable, [], "??"}
         ]}

      assert {:tuple, _,
              [
                {:variable, _, "?_1"},
                {:literal, _, 1},
                {:variable, _, "?_2"}
              ]} = Holes.number_anonymous(ast)
    end

    test "leaves named holes alone" do
      ast = {:variable, [], "?body"}
      assert {:variable, _, "?body"} = Holes.number_anonymous(ast)
    end
  end
end
