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

  describe "filter_s / reject / merge" do
    test "filter_s keeps a value when the predicate is true" do
      assert @sig.filter_s(fn x -> x > 3 end, {:sig, {:some, 5}}) == {:sig, {:some, 5}}
    end

    test "filter_s drops a value when the predicate is false" do
      assert @sig.filter_s(fn x -> x > 3 end, {:sig, {:some, 1}}) == {:sig, {:none}}
    end

    test "reject is the inverse of filter_s" do
      assert @sig.reject(fn x -> x > 3 end, {:sig, {:some, 5}}) == {:sig, {:none}}
      assert @sig.reject(fn x -> x > 3 end, {:sig, {:some, 1}}) == {:sig, {:some, 1}}
    end

    test "merge is left-biased" do
      assert @sig.merge({:sig, {:some, 1}}, {:sig, {:some, 2}}) == {:sig, {:some, 1}}
      assert @sig.merge({:sig, {:none}}, {:sig, {:some, 2}}) == {:sig, {:some, 2}}
      assert @sig.merge({:sig, {:none}}, {:sig, {:none}}) == {:sig, {:none}}
    end
  end

  # f for foldp is curried: f(val)(state). Running-sum folder.
  # (A function literal can't live in a module attribute, so use a helper.)
  defp sum_folder, do: fn v -> fn s -> v + s end end

  describe "foldp" do
    test "present tick folds and emits the new state" do
      assert @sig.foldp(sum_folder(), 10, {:sig, {:some, 5}}) == {{:sig, {:some, 15}}, 15}
    end

    test "absent tick is a no-op: emits absent, state unchanged" do
      assert @sig.foldp(sum_folder(), 10, {:sig, {:none}}) == {{:sig, {:none}}, 10}
    end

    test "state hands off correctly across two consecutive present ticks" do
      {_sig1, st1} = @sig.foldp(sum_folder(), 0, {:sig, {:some, 3}})
      assert {{:sig, {:some, 7}}, 7} = @sig.foldp(sum_folder(), st1, {:sig, {:some, 4}})
    end
  end

  describe "drop_repeats / latch / count" do
    test "drop_repeats passes the first value and remembers it" do
      assert @sig.drop_repeats({:none}, {:sig, {:some, 7}}) == {{:sig, {:some, 7}}, {:some, 7}}
    end

    test "drop_repeats suppresses a value equal to the previous, state unchanged" do
      assert @sig.drop_repeats({:some, 7}, {:sig, {:some, 7}}) == {{:sig, {:none}}, {:some, 7}}
    end

    test "drop_repeats passes a value different from the previous" do
      assert @sig.drop_repeats({:some, 7}, {:sig, {:some, 8}}) == {{:sig, {:some, 8}}, {:some, 8}}
    end

    test "drop_repeats absent tick keeps prev unchanged" do
      assert @sig.drop_repeats({:some, 7}, {:sig, {:none}}) == {{:sig, {:none}}, {:some, 7}}
    end

    test "latch emits and remembers a present value" do
      assert @sig.latch(0, {:sig, {:some, 9}}) == {{:sig, {:some, 9}}, 9}
    end

    test "latch re-emits the remembered value on an absent tick" do
      assert @sig.latch(9, {:sig, {:none}}) == {{:sig, {:some, 9}}, 9}
    end

    test "count increments only on present ticks" do
      assert @sig.count(2, {:sig, {:some, :anything}}) == {{:sig, {:some, 3}}, 3}
      assert @sig.count(2, {:sig, {:none}}) == {{:sig, {:none}}, 2}
    end
  end

  describe "every" do
    test "fires when the interval has elapsed, emitting now and updating state" do
      assert @sig.every(1000, 1000, 0) == {{:sig, {:some, 1000}}, 1000}
    end

    test "does not fire before the interval elapses, state unchanged" do
      assert @sig.every(1000, 1500, 1000) == {{:sig, {:none}}, 1000}
    end

    test "fires exactly at the interval boundary (>=)" do
      assert @sig.every(1000, 2000, 1000) == {{:sig, {:some, 2000}}, 2000}
    end
  end

  describe "rising_edge / falling_edge" do
    test "rising_edge fires on false->true, emitting unit, state becomes true" do
      assert @sig.rising_edge(false, {:sig, {:some, true}}) == {{:sig, {:some, nil}}, true}
    end

    test "rising_edge does not fire when level stays true" do
      assert @sig.rising_edge(true, {:sig, {:some, true}}) == {{:sig, {:none}}, true}
    end

    test "rising_edge absent tick keeps prev level" do
      assert @sig.rising_edge(true, {:sig, {:none}}) == {{:sig, {:none}}, true}
    end

    test "falling_edge fires on true->false, emitting unit, state becomes false" do
      assert @sig.falling_edge(true, {:sig, {:some, false}}) == {{:sig, {:some, nil}}, false}
    end

    test "falling_edge does not fire when level stays false" do
      assert @sig.falling_edge(false, {:sig, {:some, false}}) == {{:sig, {:none}}, false}
    end
  end

  describe "debounce" do
    @init {{:none}, 0}

    test "first appearance starts timing, emits absent, records candidate+since" do
      assert @sig.debounce(50, 100, @init, {:sig, {:some, 7}}) ==
               {{:sig, {:none}}, {{:some, 7}, 100}}
    end

    test "same value before interval elapses stays absent, since unchanged" do
      st = {{:some, 7}, 100}
      assert @sig.debounce(50, 130, st, {:sig, {:some, 7}}) == {{:sig, {:none}}, st}
    end

    test "same value after interval elapses emits the value" do
      st = {{:some, 7}, 100}
      assert @sig.debounce(50, 160, st, {:sig, {:some, 7}}) ==
               {{:sig, {:some, 7}}, {{:some, 7}, 160}}
    end

    test "a different value restarts timing from now" do
      st = {{:some, 7}, 100}
      assert @sig.debounce(50, 120, st, {:sig, {:some, 9}}) ==
               {{:sig, {:none}}, {{:some, 9}, 120}}
    end

    test "absent tick is a no-op: emits absent, state unchanged" do
      st = {{:some, 7}, 100}
      assert @sig.debounce(50, 200, st, {:sig, {:none}}) == {{:sig, {:none}}, st}
    end
  end

  describe "with_default" do
    test "returns the present value" do
      assert @sig.with_default(-1, {:sig, {:some, 42}}) == 42
    end

    test "returns the default when absent" do
      assert @sig.with_default(-1, {:sig, {:none}}) == -1
    end
  end
end
