defmodule Cure.Stdlib.IterTest do
  use ExUnit.Case, async: false

  setup_all do
    Cure.Stdlib.Preload.preload(examples: false)
    :ok
  end

  describe "Std.Iter basics" do
    test "from_list + to_list is the identity" do
      it = :"Cure.Std.Iter".from_list([1, 2, 3, 4])
      assert :"Cure.Std.Iter".to_list(it) == [1, 2, 3, 4]
    end

    test "range enumerates inclusively" do
      it = :"Cure.Std.Iter".range(1, 5)
      assert :"Cure.Std.Iter".to_list(it) == [1, 2, 3, 4, 5]
    end

    test "empty iterator is empty" do
      it = :"Cure.Std.Iter".empty()
      assert :"Cure.Std.Iter".to_list(it) == []
    end

    test "take stops early without forcing the tail" do
      # Use a very large range; take 3 should return [1, 2, 3] quickly.
      it = :"Cure.Std.Iter".range(1, 10_000_000)
      assert :"Cure.Std.Iter".take(it, 3) == [1, 2, 3]
    end

    test "fold sums a range" do
      # fold(range(1..5), 0, fn x -> fn acc -> x + acc)
      it = :"Cure.Std.Iter".range(1, 5)
      add = fn x -> fn acc -> x + acc end end
      assert :"Cure.Std.Iter".fold(it, 0, add) == 15
    end
  end
end
