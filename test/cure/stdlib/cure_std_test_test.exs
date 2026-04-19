defmodule :cure_std_test_test do
  use ExUnit.Case, async: true

  test "forall_shrunk passes when property holds" do
    gen = fn _ -> 1 end
    property = fn n -> n > 0 end
    assert :ok = :cure_std_test.forall_shrunk(gen, property, 10)
  end

  test "forall_shrunk raises with a shrunk counterexample" do
    gen = fn _ -> 100 end
    # Property: "n is less than 50" -- fails for 100, shrinks toward 50.
    property = fn n -> n < 50 end

    try do
      :cure_std_test.forall_shrunk(gen, property, 5)
      flunk("expected property to fail")
    rescue
      e in ErlangError ->
        assert {:property_failed_with_shrunk, value} = e.original
        # Shrinker must converge to a value at least as small as the original.
        assert value <= 100
    end
  end
end
