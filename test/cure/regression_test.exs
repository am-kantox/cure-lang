defmodule Cure.RegressionTest do
  use ExUnit.Case, async: false

  @moduledoc """
  End-to-end regression coverage. These tests invoke the same logic as
  `mix cure.check` so a plain `mix test` run catches stdlib or example
  regressions too.
  """

  alias Mix.Tasks.Cure.Check

  @tag :regression
  test "every Std.* module compiles without warnings" do
    result =
      ExUnit.CaptureIO.capture_io(fn ->
        try do
          Check.Stdlib.run([])
        catch
          :exit, {:shutdown, 1} -> flunk("stdlib regression failed")
        end
      end)

    assert result =~ "stdlib: 20 passed, 0 failed"
  end

  @tag :regression
  test "every example compiles and produces the expected output" do
    preload_stdlib()

    result =
      ExUnit.CaptureIO.capture_io(fn ->
        try do
          Check.Examples.run([])
        catch
          :exit, {:shutdown, 1} -> flunk("examples regression failed")
        end
      end)

    refute result =~ "FAIL"
    assert result =~ ~r/examples: \d+ passed, 0 failed/
  end

  defp preload_stdlib do
    for dir <- ["_build/cure/ebin", "_build/cure/ex_ebin"] do
      if File.dir?(dir), do: :code.add_patha(String.to_charlist(Path.expand(dir)))
    end

    for name <-
          ~w(Core List Pair Math String Io System Show Option Result
             Eq Ord Functor Map Set Test Vector Equal Refine Fsm) do
      _ = Code.ensure_loaded(String.to_atom("Cure.Std.#{name}"))
    end
  end
end
