defmodule Cure.Doc.DoctestsTest do
  use ExUnit.Case, async: true

  alias Cure.Doc.Doctests

  describe "extract_from_source/1" do
    test "captures a single cure>/=> pair" do
      src = """
      ## Adds two ints.
      ##
      ##   cure> Demo.add(2, 3)
      ##   => 5
      fn add(a: Int, b: Int) -> Int = a + b
      """

      assert [%{name: "add_2", expr: "Demo.add(2, 3)", expected: "5"}] =
               Doctests.extract_from_source(src)
    end

    test "captures multiple pairs in one block" do
      src = """
      ## Demo.
      ##   cure> Demo.add(1, 2)
      ##   => 3
      ##   cure> Demo.add(10, -4)
      ##   => 6
      fn add(a: Int, b: Int) -> Int = a + b
      """

      cases = Doctests.extract_from_source(src)
      assert length(cases) == 2
      assert Enum.all?(cases, fn %{expr: e} -> String.starts_with?(e, "Demo.add") end)
    end

    test "ignores cure> without =>" do
      src = """
      ## Lonely.
      ##   cure> Demo.foo()
      fn foo() -> Int = 0
      """

      assert [] = Doctests.extract_from_source(src)
    end

    test "no doctests means empty list" do
      src = "mod Demo\n  fn nothing() -> Int = 0\n"
      assert [] = Doctests.extract_from_source(src)
    end
  end
end
