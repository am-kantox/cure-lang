defmodule Cure.Compiler.ErrorsV17Test do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Errors

  @new_codes ~w(E011 E012 E013 E014 E015 E016 E017 E018 E019 E020)

  describe "extended error catalog" do
    for code <- @new_codes do
      test "explain/#{code}" do
        assert {:ok, text} = Errors.explain(unquote(code))
        assert text =~ unquote(code)
        assert text =~ "Fix:"
      end
    end

    test "unknown code returns :error" do
      assert :error = Errors.explain("E999")
    end

    test "case-insensitive lookup" do
      assert {:ok, _} = Errors.explain("e017")
    end
  end
end
