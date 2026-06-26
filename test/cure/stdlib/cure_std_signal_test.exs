defmodule Cure.Stdlib.SignalTest do
  use ExUnit.Case, async: false

  # `Cure.Std.Signal` is loaded dynamically by `Cure.Stdlib.Preload` in
  # `setup_all`; silence the compile-time "module not available" warning.
  @compile {:no_warn_undefined, :"Cure.Std.Signal"}
  @sig :"Cure.Std.Signal"

  setup_all do
    Cure.Stdlib.Preload.preload(examples: false, kind: :all)
    :ok
  end

  describe "sources" do
    test "constant/1 is an always-present signal" do
      assert @sig.constant(5) == {:sig, {:some, 5}}
    end

    test "never/0 is an always-absent signal" do
      assert @sig.never() == {:sig, {:none}}
    end
  end

  describe "map / mapTo / toUnit" do
    test "map applies f to a present value" do
      assert @sig.map(fn x -> x * 2 end, {:sig, {:some, 5}}) == {:sig, {:some, 10}}
    end

    test "map preserves absence" do
      assert @sig.map(fn x -> x * 2 end, {:sig, {:none}}) == {:sig, {:none}}
    end

    test "map_to replaces a present value with a constant" do
      assert @sig.map_to(:hit, {:sig, {:some, 99}}) == {:sig, {:some, :hit}}
      assert @sig.map_to(:hit, {:sig, {:none}}) == {:sig, {:none}}
    end

    test "to_unit maps a present value to the unit value nil" do
      assert @sig.to_unit({:sig, {:some, 7}}) == {:sig, {:some, nil}}
      assert @sig.to_unit({:sig, {:none}}) == {:sig, {:none}}
    end
  end
end
