defmodule :cure_std_test do
  @moduledoc """
  Runtime helpers for `Std.Test.forall_shrunk/3` (v0.23.0).

  When a property fails, walk `Std.Gen.shrink/1` candidates in
  aggressive-first order and pick the smallest value that still makes
  the property return `false`. Raise `{:property_failed_with_shrunk,
  minimal_value}` carrying the minimised counterexample.
  """

  def forall_shrunk(gen, property, runs) when is_function(gen) and is_function(property) do
    case find_counterexample(gen, property, runs) do
      :all_pass ->
        :ok

      {:failed, value} ->
        minimal = shrink_loop(value, property)
        :erlang.error({:property_failed_with_shrunk, minimal})
    end
  end

  defp find_counterexample(_gen, _property, 0), do: :all_pass

  defp find_counterexample(gen, property, n) when n > 0 do
    value = gen.(:draw)

    case property.(value) do
      true -> find_counterexample(gen, property, n - 1)
      false -> {:failed, value}
      _ -> {:failed, value}
    end
  end

  defp shrink_loop(value, property) do
    candidates =
      try do
        :cure_std_gen.shrink(value)
      rescue
        _ -> []
      end

    failing =
      Enum.find(candidates, fn cand ->
        case safe_invoke(property, cand) do
          false -> true
          _ -> false
        end
      end)

    case failing do
      nil -> value
      better -> shrink_loop(better, property)
    end
  end

  defp safe_invoke(f, v) do
    try do
      f.(v)
    rescue
      _ -> false
    catch
      _, _ -> false
    end
  end
end
