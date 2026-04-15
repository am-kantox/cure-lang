defmodule CureTest do
  use ExUnit.Case
  doctest Cure

  test "version returns a string" do
    assert is_binary(Cure.version())
  end
end
