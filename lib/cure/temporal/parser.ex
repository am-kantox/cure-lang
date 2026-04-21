defmodule Cure.Temporal.Parser do
  @moduledoc """
  Parser for the `temporal` DSL (v0.27.0).

  Accepts a single-formula string or a multi-property script where
  properties are separated by newlines or semicolons. Parentheses
  group precedence; the operator precedence table (lowest to highest)
  is:

      ;                 (property separator)
      ->                (implication)
      or
      and
      until
      never, !
      always, eventually, next
      (atoms, parens)

  Atom names are any `[A-Za-z_][A-Za-z0-9_.]*` identifier.

  The entry point `parse/1` returns `{:ok, [formula, ...]}` for a
  multi-property script and `{:error, reason}` when the input cannot
  be parsed.
  """

  alias Cure.Temporal.Formula

  @type result :: {:ok, [Formula.t()]} | {:error, term()}

  @doc "Parse a temporal-DSL string into a list of formulae."
  @spec parse(String.t()) :: result()
  def parse(src) when is_binary(src) do
    case tokenize(src) do
      {:ok, tokens} ->
        parse_script(tokens, [])

      {:error, _} = err ->
        err
    end
  end

  @doc """
  Parse a single formula. Returns `{:ok, formula}` or `{:error, _}`.

  Convenience for callers that know their input is one property.
  """
  @spec parse_one(String.t()) :: {:ok, Formula.t()} | {:error, term()}
  def parse_one(src) do
    case parse(src) do
      {:ok, [f]} -> {:ok, f}
      {:ok, []} -> {:error, :empty_formula}
      {:ok, _} -> {:error, :expected_single_formula}
      {:error, _} = err -> err
    end
  end

  # -- Top-level script --------------------------------------------------------

  defp parse_script([], acc), do: {:ok, Enum.reverse(acc)}

  defp parse_script(tokens, acc) do
    case parse_formula(tokens) do
      {:ok, formula, rest} ->
        case rest do
          [] -> {:ok, Enum.reverse([formula | acc])}
          [{:semi, _} | rest1] -> parse_script(rest1, [formula | acc])
          other -> {:error, {:unexpected, other}}
        end

      {:error, _} = err ->
        err
    end
  end

  # -- Formula with precedence climbing ---------------------------------------
  # Lowest precedence: implication. Right-associative.

  defp parse_formula(tokens) do
    with {:ok, left, rest} <- parse_or(tokens) do
      case rest do
        [{:arrow, _} | rest1] ->
          with {:ok, right, rest2} <- parse_formula(rest1) do
            {:ok, Formula.implies(left, right), rest2}
          end

        _ ->
          {:ok, left, rest}
      end
    end
  end

  defp parse_or(tokens) do
    with {:ok, left, rest} <- parse_and(tokens) do
      case rest do
        [{:or, _} | rest1] ->
          with {:ok, right, rest2} <- parse_or(rest1) do
            {:ok, Formula.or_(left, right), rest2}
          end

        _ ->
          {:ok, left, rest}
      end
    end
  end

  defp parse_and(tokens) do
    with {:ok, left, rest} <- parse_until(tokens) do
      case rest do
        [{:and, _} | rest1] ->
          with {:ok, right, rest2} <- parse_and(rest1) do
            {:ok, Formula.and_(left, right), rest2}
          end

        _ ->
          {:ok, left, rest}
      end
    end
  end

  defp parse_until(tokens) do
    with {:ok, left, rest} <- parse_unary(tokens) do
      case rest do
        [{:until, _} | rest1] ->
          with {:ok, right, rest2} <- parse_until(rest1) do
            {:ok, Formula.until(left, right), rest2}
          end

        _ ->
          {:ok, left, rest}
      end
    end
  end

  defp parse_unary([{:always, _} | rest]) do
    with {:ok, p, rest1} <- parse_unary(rest) do
      {:ok, Formula.always(p), rest1}
    end
  end

  defp parse_unary([{:eventually, _} | rest]) do
    with {:ok, p, rest1} <- parse_unary(rest) do
      {:ok, Formula.eventually(p), rest1}
    end
  end

  defp parse_unary([{:never, _} | rest]) do
    with {:ok, p, rest1} <- parse_unary(rest) do
      {:ok, Formula.never(p), rest1}
    end
  end

  defp parse_unary([{:next, _} | rest]) do
    with {:ok, p, rest1} <- parse_unary(rest) do
      {:ok, Formula.next_(p), rest1}
    end
  end

  defp parse_unary([{:bang, _} | rest]) do
    with {:ok, p, rest1} <- parse_unary(rest) do
      {:ok, Formula.not_(p), rest1}
    end
  end

  defp parse_unary(tokens), do: parse_atom(tokens)

  defp parse_atom([{:lparen, _} | rest]) do
    with {:ok, f, rest1} <- parse_formula(rest) do
      case rest1 do
        [{:rparen, _} | rest2] -> {:ok, f, rest2}
        other -> {:error, {:expected, :rparen, got: other}}
      end
    end
  end

  defp parse_atom([{:tt, _} | rest]), do: {:ok, Formula.tt(), rest}
  defp parse_atom([{:ff, _} | rest]), do: {:ok, Formula.ff(), rest}
  defp parse_atom([{:ident, _, name} | rest]), do: {:ok, Formula.atom(name), rest}
  defp parse_atom(tokens), do: {:error, {:expected_atom, got: tokens}}

  # -- Tokeniser ---------------------------------------------------------------

  @keywords %{
    "always" => :always,
    "eventually" => :eventually,
    "never" => :never,
    "next" => :next,
    "and" => :and,
    "or" => :or,
    "until" => :until,
    "true" => :tt,
    "false" => :ff
  }

  defp tokenize(src) do
    try do
      tokens = do_tokenize(src, 1, [])
      {:ok, Enum.reverse(tokens)}
    catch
      {:lex_error, _} = err -> {:error, err}
    end
  end

  defp do_tokenize("", _line, acc), do: acc

  defp do_tokenize("\n" <> rest, line, acc),
    do: do_tokenize(rest, line + 1, [{:semi, line} | acc])

  defp do_tokenize(";" <> rest, line, acc),
    do: do_tokenize(rest, line, [{:semi, line} | acc])

  defp do_tokenize("->" <> rest, line, acc),
    do: do_tokenize(rest, line, [{:arrow, line} | acc])

  defp do_tokenize("(" <> rest, line, acc),
    do: do_tokenize(rest, line, [{:lparen, line} | acc])

  defp do_tokenize(")" <> rest, line, acc),
    do: do_tokenize(rest, line, [{:rparen, line} | acc])

  defp do_tokenize("!" <> rest, line, acc),
    do: do_tokenize(rest, line, [{:bang, line} | acc])

  defp do_tokenize(" " <> rest, line, acc), do: do_tokenize(rest, line, acc)
  defp do_tokenize("\t" <> rest, line, acc), do: do_tokenize(rest, line, acc)
  defp do_tokenize("\r" <> rest, line, acc), do: do_tokenize(rest, line, acc)

  defp do_tokenize(<<c::utf8, _::binary>> = src, line, acc) when c in ?a..?z or c in ?A..?Z or c == ?_ do
    {ident, rest} = take_ident(src, "")

    case Map.get(@keywords, ident) do
      nil -> do_tokenize(rest, line, [{:ident, line, ident} | acc])
      key -> do_tokenize(rest, line, [{key, line} | acc])
    end
  end

  defp do_tokenize(other, line, _acc),
    do: throw({:lex_error, {:unexpected, String.slice(other, 0, 8), line}})

  defp take_ident(<<c::utf8, rest::binary>>, acc)
       when c in ?a..?z or c in ?A..?Z or c in ?0..?9 or c == ?_ or c == ?. do
    take_ident(rest, acc <> <<c::utf8>>)
  end

  defp take_ident(rest, acc), do: {acc, rest}
end
