defmodule Cure.Project.Json do
  @moduledoc """
  Minimal internal JSON codec (v0.23.0).

  Used by `Cure.Project.Registry`, `Cure.Project.Lock`,
  `Cure.Project.Signing`, and `Cure.Project.Transparency` so that the
  core compiler does not pick up an external JSON dependency.

  The codec is self-contained, RFC 8259 compliant for the subset the
  registry speaks (objects, arrays, strings, numbers, `true` / `false` /
  `null`). It is intentionally strict: trailing commas, comments, and
  unquoted keys are rejected.

  The public stdlib-facing JSON API is `Std.Json` (see
  `lib/std/json.cure`). This module exists purely so that registry /
  lockfile / signing code can run before the stdlib beams are loaded.
  """

  # -- Encoder ----------------------------------------------------------------

  @doc """
  Encode an Elixir term to a JSON string.

  Supports atoms (`nil` -> `null`, `true` / `false` -> booleans, other
  atoms -> string), integers, floats, binaries, lists, and maps whose
  keys are atoms or strings. Anything else raises `ArgumentError`.
  """
  @spec encode(term()) :: String.t()
  def encode(nil), do: "null"
  def encode(true), do: "true"
  def encode(false), do: "false"
  def encode(n) when is_integer(n), do: Integer.to_string(n)

  def encode(f) when is_float(f) do
    # Use :io_lib.format with ~p so integer-valued floats round-trip as
    # `42.0` instead of `4.2e1`; fall back to Float.to_string/1 for the
    # general case.
    Float.to_string(f)
  end

  def encode(atom) when is_atom(atom), do: encode(Atom.to_string(atom))

  def encode(s) when is_binary(s) do
    <<?", escape(s)::binary, ?">>
  end

  def encode(list) when is_list(list) do
    inner = Enum.map_join(list, ",", &encode/1)
    "[" <> inner <> "]"
  end

  def encode(map) when is_map(map) do
    inner =
      map
      |> Enum.map(fn {k, v} ->
        key =
          cond do
            is_atom(k) -> Atom.to_string(k)
            is_binary(k) -> k
            true -> raise ArgumentError, "json keys must be atoms or binaries, got: #{inspect(k)}"
          end

        encode(key) <> ":" <> encode(v)
      end)
      |> Enum.join(",")

    "{" <> inner <> "}"
  end

  def encode(other) do
    raise ArgumentError, "cannot encode term as JSON: #{inspect(other)}"
  end

  defp escape(s), do: escape(s, <<>>)

  defp escape(<<>>, acc), do: acc
  defp escape(<<?", rest::binary>>, acc), do: escape(rest, acc <> "\\\"")
  defp escape(<<?\\, rest::binary>>, acc), do: escape(rest, acc <> "\\\\")
  defp escape(<<?\n, rest::binary>>, acc), do: escape(rest, acc <> "\\n")
  defp escape(<<?\r, rest::binary>>, acc), do: escape(rest, acc <> "\\r")
  defp escape(<<?\t, rest::binary>>, acc), do: escape(rest, acc <> "\\t")
  defp escape(<<?\b, rest::binary>>, acc), do: escape(rest, acc <> "\\b")
  defp escape(<<?\f, rest::binary>>, acc), do: escape(rest, acc <> "\\f")

  defp escape(<<c::utf8, rest::binary>>, acc) when c < 0x20 do
    hex = c |> Integer.to_string(16) |> String.pad_leading(4, "0")
    escape(rest, acc <> "\\u" <> hex)
  end

  defp escape(<<c::utf8, rest::binary>>, acc) do
    escape(rest, acc <> <<c::utf8>>)
  end

  # -- Decoder ----------------------------------------------------------------

  @doc """
  Decode a JSON string into Elixir terms.

  Returns `{:ok, value}` or `{:error, {reason, position}}`. Positions
  are 0-based byte offsets.

  Objects decode to maps with string keys. Arrays decode to lists.
  Numbers decode to integers or floats. `null` decodes to `nil`.
  """
  @spec decode(String.t()) :: {:ok, term()} | {:error, {atom(), non_neg_integer()}}
  def decode(s) when is_binary(s) do
    case value(skip_ws(s, 0)) do
      {:ok, v, rest, pos} ->
        case skip_ws(rest, pos) do
          {<<>>, _} -> {:ok, v}
          {other, p} when is_binary(other) -> {:error, {:trailing_data, p}}
        end

      {:error, _} = err ->
        err
    end
  end

  # Returns `{:ok, value, rest, new_pos}` or `{:error, {reason, pos}}`.
  defp value({<<>>, pos}), do: {:error, {:unexpected_eof, pos}}

  defp value({<<?{, rest::binary>>, pos}), do: object(skip_ws(rest, pos + 1), %{}, :first)

  defp value({<<?[, rest::binary>>, pos}), do: array(skip_ws(rest, pos + 1), [], :first)

  defp value({<<?", rest::binary>>, pos}) do
    case string(rest, <<>>, pos + 1) do
      {:ok, str, rest2, p} -> {:ok, str, rest2, p}
      err -> err
    end
  end

  defp value({<<"true", rest::binary>>, pos}), do: {:ok, true, rest, pos + 4}
  defp value({<<"false", rest::binary>>, pos}), do: {:ok, false, rest, pos + 5}
  defp value({<<"null", rest::binary>>, pos}), do: {:ok, nil, rest, pos + 4}

  defp value({<<c, _::binary>> = bin, pos}) when c in ?0..?9 or c == ?-, do: number(bin, pos)

  defp value({_other, pos}), do: {:error, {:invalid_token, pos}}

  defp object({<<>>, pos}, _acc, _state), do: {:error, {:unexpected_eof, pos}}

  defp object({<<?}, rest::binary>>, pos}, acc, _state), do: {:ok, acc, rest, pos + 1}

  defp object({<<?,, rest::binary>>, pos}, acc, :more) do
    object(skip_ws(rest, pos + 1), acc, :first)
  end

  defp object({<<?", rest::binary>>, pos}, acc, _state) do
    with {:ok, key, rest2, p2} <- string(rest, <<>>, pos + 1),
         {<<?:, rest3::binary>>, p3} <- skip_ws(rest2, p2),
         {:ok, val, rest4, p4} <- value(skip_ws(rest3, p3 + 1)) do
      object(skip_ws(rest4, p4), Map.put(acc, key, val), :more)
    else
      {:error, _} = err -> err
      {_, p} -> {:error, {:expected_colon, p}}
    end
  end

  defp object({_bin, pos}, _acc, _state), do: {:error, {:expected_key, pos}}

  defp array({<<>>, pos}, _acc, _state), do: {:error, {:unexpected_eof, pos}}

  defp array({<<?], rest::binary>>, pos}, acc, _state), do: {:ok, Enum.reverse(acc), rest, pos + 1}

  defp array({<<?,, rest::binary>>, pos}, acc, :more) do
    array(skip_ws(rest, pos + 1), acc, :first)
  end

  defp array({bin, pos}, acc, _state) do
    case value({bin, pos}) do
      {:ok, v, rest, p} -> array(skip_ws(rest, p), [v | acc], :more)
      {:error, _} = err -> err
    end
  end

  defp string(<<>>, _acc, pos), do: {:error, {:unterminated_string, pos}}

  defp string(<<?", rest::binary>>, acc, pos), do: {:ok, acc, rest, pos + 1}

  defp string(<<?\\, ?", rest::binary>>, acc, pos), do: string(rest, acc <> "\"", pos + 2)
  defp string(<<?\\, ?\\, rest::binary>>, acc, pos), do: string(rest, acc <> "\\", pos + 2)
  defp string(<<?\\, ?/, rest::binary>>, acc, pos), do: string(rest, acc <> "/", pos + 2)
  defp string(<<?\\, ?n, rest::binary>>, acc, pos), do: string(rest, acc <> "\n", pos + 2)
  defp string(<<?\\, ?r, rest::binary>>, acc, pos), do: string(rest, acc <> "\r", pos + 2)
  defp string(<<?\\, ?t, rest::binary>>, acc, pos), do: string(rest, acc <> "\t", pos + 2)
  defp string(<<?\\, ?b, rest::binary>>, acc, pos), do: string(rest, acc <> "\b", pos + 2)
  defp string(<<?\\, ?f, rest::binary>>, acc, pos), do: string(rest, acc <> "\f", pos + 2)

  defp string(<<?\\, ?u, h1, h2, h3, h4, rest::binary>>, acc, pos) do
    case Integer.parse(<<h1, h2, h3, h4>>, 16) do
      {cp, ""} -> string(rest, acc <> <<cp::utf8>>, pos + 6)
      _ -> {:error, {:invalid_escape, pos}}
    end
  end

  defp string(<<?\\, _c, _rest::binary>>, _acc, pos), do: {:error, {:invalid_escape, pos}}

  defp string(<<c::utf8, rest::binary>>, acc, pos) do
    string(rest, acc <> <<c::utf8>>, pos + byte_size(<<c::utf8>>))
  end

  defp number(bin, pos) do
    {head, rest} = take_number(bin, <<>>)

    cond do
      head == <<>> ->
        {:error, {:invalid_number, pos}}

      String.contains?(head, ".") or String.contains?(head, "e") or String.contains?(head, "E") ->
        case Float.parse(head) do
          {f, ""} -> {:ok, f, rest, pos + byte_size(head)}
          _ -> {:error, {:invalid_number, pos}}
        end

      true ->
        case Integer.parse(head) do
          {i, ""} -> {:ok, i, rest, pos + byte_size(head)}
          _ -> {:error, {:invalid_number, pos}}
        end
    end
  end

  defp take_number(<<>>, acc), do: {acc, <<>>}

  defp take_number(<<c, rest::binary>>, acc)
       when c in ?0..?9 or c in [?-, ?+, ?., ?e, ?E] do
    take_number(rest, acc <> <<c>>)
  end

  defp take_number(other, acc), do: {acc, other}

  defp skip_ws(<<>>, pos), do: {<<>>, pos}

  defp skip_ws(<<c, rest::binary>>, pos) when c in [?\s, ?\t, ?\n, ?\r] do
    skip_ws(rest, pos + 1)
  end

  defp skip_ws(bin, pos), do: {bin, pos}
end
