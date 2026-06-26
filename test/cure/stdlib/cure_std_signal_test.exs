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
end
