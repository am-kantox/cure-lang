defmodule Cure.Types.DeriveTest do
  use ExUnit.Case, async: true

  alias Cure.Types.Derive

  describe "derive :show" do
    test "no fields returns type name string literal" do
      [{:function_def, _meta, [body]}] = Derive.derive(:show, "Empty", [])
      assert {:literal, [subtype: :string], "Empty"} = body
    end

    test "single field builds concatenation AST" do
      [{:function_def, _meta, [body]}] = Derive.derive(:show, "Wrapper", [:value])
      assert {:binary_op, [operator: :<>, category: :string], _} = body
    end

    test "two fields include separator" do
      [{:function_def, meta, [body]}] = Derive.derive(:show, "Point", [:x, :y])
      assert Keyword.get(meta, :name) == "show"
      assert Keyword.get(meta, :arity) == 1

      # The body should be a chain of <> operators containing ", " separator
      ast_string = inspect(body)
      assert ast_string =~ "x: "
      assert ast_string =~ "y: "
      assert ast_string =~ ", "
      assert ast_string =~ "Point{"
    end
  end

  describe "derive :eq" do
    test "generates structural equality" do
      [{:function_def, meta, [body]}] = Derive.derive(:eq, "Point", [:x, :y])
      assert Keyword.get(meta, :name) == "eq"
      assert Keyword.get(meta, :arity) == 2
      assert {:binary_op, [operator: :==, category: :comparison], _} = body
    end
  end

  describe "derive :ord" do
    test "generates comparison function" do
      [{:function_def, meta, [body]}] = Derive.derive(:ord, "Point", [:x, :y])
      assert Keyword.get(meta, :name) == "compare"
      assert Keyword.get(meta, :arity) == 2
      assert {:conditional, _, _} = body
    end
  end

  describe "can_derive?" do
    test "supported typeclasses" do
      assert Derive.can_derive?(:show)
      assert Derive.can_derive?(:eq)
      assert Derive.can_derive?(:ord)
    end

    test "unsupported typeclasses" do
      refute Derive.can_derive?(:hash)
      refute Derive.can_derive?(:serialize)
    end
  end

  describe "unknown typeclass" do
    test "returns empty list" do
      assert [] = Derive.derive(:unknown, "Foo", [:a])
    end
  end
end
