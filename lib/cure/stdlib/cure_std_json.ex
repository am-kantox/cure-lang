defmodule :cure_std_json do
  @moduledoc """
  Runtime helpers for `Std.Json` (v0.23.0).

  These Erlang-style functions are the targets of the `@extern` bridges
  in `lib/std/json.cure`. Every function here is pure and stateless.

  The wire shape of a Cure ADT value is `{tag, payload_tuple}` for
  non-nullary constructors and the bare atom `tag` for nullary ones --
  the same representation `Cure.Types.Derive` emits.
  """

  # -- Encoder -----------------------------------------------------------------

  @doc "Encode a `Std.Json.Value` tagged tuple to a JSON string."
  def encode(:null), do: "null"
  def encode({:bool, true}), do: "true"
  def encode({:bool, false}), do: "false"
  def encode({:num, f}) when is_float(f), do: float_to_string(f)
  def encode({:num, i}) when is_integer(i), do: Integer.to_string(i)
  def encode({:str, s}) when is_binary(s), do: Cure.Project.Json.encode(s)

  def encode({:arr, xs}) when is_list(xs) do
    inner = Enum.map_join(xs, ",", &encode/1)
    "[" <> inner <> "]"
  end

  def encode({:obj, kvs}) when is_list(kvs) do
    inner =
      Enum.map_join(kvs, ",", fn {k, v} ->
        Cure.Project.Json.encode(k) <> ":" <> encode(v)
      end)

    "{" <> inner <> "}"
  end

  # Accept the struct/record form some front-ends may emit.
  def encode(other), do: raise(ArgumentError, "cannot encode: #{inspect(other)}")

  # -- Decoder -----------------------------------------------------------------

  @doc "Decode a JSON string into a `Std.Json.Value` tagged tuple."
  def decode(src) when is_binary(src) do
    case Cure.Project.Json.decode(src) do
      {:ok, term} -> {:ok, to_value(term)}
      {:error, {reason, pos}} -> {:error, :erlang.iolist_to_binary(~c"#{reason} at offset #{pos}")}
    end
  end

  defp to_value(nil), do: :null
  defp to_value(true), do: {:bool, true}
  defp to_value(false), do: {:bool, false}
  defp to_value(n) when is_integer(n), do: {:num, n * 1.0}
  defp to_value(n) when is_float(n), do: {:num, n}
  defp to_value(s) when is_binary(s), do: {:str, s}

  defp to_value(list) when is_list(list) do
    {:arr, Enum.map(list, &to_value/1)}
  end

  defp to_value(map) when is_map(map) do
    {:obj, Enum.map(map, fn {k, v} -> {k, to_value(v)} end)}
  end

  # -- Construction helpers ---------------------------------------------------

  @doc "Widen a Cure Int into a JSON number Value."
  def num_of_int(n) when is_integer(n), do: {:num, n * 1.0}

  # -- Private ----------------------------------------------------------------

  defp float_to_string(f) when is_float(f) do
    cond do
      f == trunc(f) -> :erlang.float_to_binary(f, [{:decimals, 1}])
      true -> :erlang.float_to_binary(f, [{:compact, []}, {:decimals, 15}])
    end
  end
end
