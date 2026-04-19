defmodule :cure_std_gen_test do
  use ExUnit.Case, async: true

  describe "shrink_int/1" do
    test "returns an empty list for 0" do
      assert [] = :cure_std_gen.shrink_int(0)
    end

    test "halves positive integers toward zero" do
      shrinks = :cure_std_gen.shrink_int(16)
      assert 0 in shrinks
      assert 8 in shrinks
      # `n - 1` is present so the shrinker can probe one step smaller.
      assert 15 in shrinks
      refute 16 in shrinks
    end

    test "symmetrically shrinks negative integers" do
      shrinks = :cure_std_gen.shrink_int(-8)
      assert 0 in shrinks
      assert 8 in shrinks
      refute -8 in shrinks
    end
  end

  describe "shrink_list/1" do
    test "returns the empty list for []" do
      assert [] = :cure_std_gen.shrink_list([])
    end

    test "includes the empty list and single-element drops" do
      shrinks = :cure_std_gen.shrink_list([1, 2, 3])
      assert [] in shrinks
      assert [1, 2] in shrinks
      assert [2, 3] in shrinks
      refute [1, 2, 3] in shrinks
    end
  end

  describe "shrink/1 polymorphic" do
    test "dispatches on runtime shape" do
      assert Enum.any?(:cure_std_gen.shrink(4), &(&1 == 0))
      assert Enum.any?(:cure_std_gen.shrink([1, 2]), &(&1 == []))
    end
  end
end
