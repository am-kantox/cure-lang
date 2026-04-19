defmodule CureBrainloop do
  @moduledoc """
  `cure_brainloop` is the v0.23.0 showcase example.

  A toy but complete expression-language interpreter driven by a Cure
  FSM. The goal is to exercise every distinguishing Cure feature
  (dependent types, ADTs, records, protocols, effects, FSMs, FFI,
  stdlib) inside a single coherent ~600-line project that any reader
  can follow end-to-end.

  ## Surface grammar

      expr := int
            | ident
            | expr + expr
            | expr - expr
            | expr * expr
            | expr / expr
            | "let" ident "=" expr "in" expr
            | "if" expr "then" expr "else" expr
            | "(" expr ")"

  ## Elixir API

      CureBrainloop.eval("let x = 2 in x * x + 1")
      #=> {:ok, 5}

      CureBrainloop.eval("bogus")
      #=> {:error, :undefined_variable}

  The evaluation is delegated to the Cure-implemented `Brainloop.Eval`
  module (compiled from `cure_src/eval.cure`) once the Cure compiler
  has processed the example, or to an Elixir fallback when the Cure
  beams are not yet available on the load path.
  """

  @type expr :: number() | {atom(), [expr()]}
  @type result :: {:ok, number()} | {:error, term()}

  @doc """
  Lex, parse, and evaluate `source`. Returns `{:ok, value}` or an
  `{:error, reason}` tuple.
  """
  @spec eval(String.t(), map()) :: result()
  def eval(source, env \\ %{}) when is_binary(source) do
    with {:ok, tokens} <- lex(source),
         {:ok, ast} <- parse(tokens),
         {:ok, value} <- evaluate(ast, env) do
      {:ok, value}
    end
  end

  # -- Lexer ------------------------------------------------------------------

  defp lex(source), do: do_lex(source, [])

  defp do_lex("", acc), do: {:ok, Enum.reverse(acc)}

  defp do_lex(<<c, rest::binary>>, acc) when c in [?\s, ?\t, ?\n] do
    do_lex(rest, acc)
  end

  defp do_lex(<<c, _::binary>> = bin, acc) when c in ?0..?9 do
    {digits, rest} = take_while(bin, &(&1 in ?0..?9))
    {n, ""} = Integer.parse(digits)
    do_lex(rest, [{:num, n} | acc])
  end

  defp do_lex(<<c, _::binary>> = bin, acc)
       when c in ?a..?z or c in ?A..?Z or c == ?_ do
    {word, rest} =
      take_while(bin, fn ch ->
        ch in ?a..?z or ch in ?A..?Z or ch in ?0..?9 or ch == ?_
      end)

    tok =
      case word do
        "let" -> {:kw, :let}
        "in" -> {:kw, :in}
        "if" -> {:kw, :if}
        "then" -> {:kw, :then}
        "else" -> {:kw, :else}
        other -> {:ident, String.to_atom(other)}
      end

    do_lex(rest, [tok | acc])
  end

  defp do_lex(<<"+", rest::binary>>, acc), do: do_lex(rest, [{:op, :+} | acc])
  defp do_lex(<<"-", rest::binary>>, acc), do: do_lex(rest, [{:op, :-} | acc])
  defp do_lex(<<"*", rest::binary>>, acc), do: do_lex(rest, [{:op, :*} | acc])
  defp do_lex(<<"/", rest::binary>>, acc), do: do_lex(rest, [{:op, :/} | acc])
  defp do_lex(<<"=", rest::binary>>, acc), do: do_lex(rest, [{:eq, nil} | acc])
  defp do_lex(<<"(", rest::binary>>, acc), do: do_lex(rest, [{:lparen, nil} | acc])
  defp do_lex(<<")", rest::binary>>, acc), do: do_lex(rest, [{:rparen, nil} | acc])

  defp do_lex(<<c, _rest::binary>>, _acc), do: {:error, {:unexpected_character, c}}

  defp take_while(bin, pred), do: take_while(bin, pred, <<>>)

  defp take_while(<<c, rest::binary>>, pred, acc) do
    if pred.(c), do: take_while(rest, pred, acc <> <<c>>), else: {acc, <<c, rest::binary>>}
  end

  defp take_while(<<>>, _pred, acc), do: {acc, <<>>}

  # -- Parser (Pratt-style) --------------------------------------------------

  defp parse(tokens) do
    case expr(tokens, 0) do
      {:ok, ast, []} -> {:ok, ast}
      {:ok, _, leftover} -> {:error, {:trailing_tokens, leftover}}
      {:error, _} = err -> err
    end
  end

  defp expr([{:kw, :let} | rest], _prec) do
    with {:ok, {:ident, name}, rest2} <- expect_ident(rest),
         {:ok, rest3} <- expect(rest2, :eq),
         {:ok, value_ast, rest4} <- expr(rest3, 0),
         {:ok, rest5} <- expect_kw(rest4, :in),
         {:ok, body_ast, rest6} <- expr(rest5, 0) do
      {:ok, {:let, name, value_ast, body_ast}, rest6}
    end
  end

  defp expr([{:kw, :if} | rest], _prec) do
    with {:ok, cond_ast, rest2} <- expr(rest, 0),
         {:ok, rest3} <- expect_kw(rest2, :then),
         {:ok, then_ast, rest4} <- expr(rest3, 0),
         {:ok, rest5} <- expect_kw(rest4, :else),
         {:ok, else_ast, rest6} <- expr(rest5, 0) do
      {:ok, {:if, cond_ast, then_ast, else_ast}, rest6}
    end
  end

  defp expr(tokens, prec) do
    with {:ok, left, rest} <- atom(tokens) do
      climb(left, rest, prec)
    end
  end

  defp climb(left, [{:op, op} | rest], prec) do
    op_prec = precedence(op)

    if op_prec >= prec do
      case expr(rest, op_prec + 1) do
        {:ok, right, rest2} -> climb({:binop, op, left, right}, rest2, prec)
        {:error, _} = err -> err
      end
    else
      {:ok, left, [{:op, op} | rest]}
    end
  end

  defp climb(left, rest, _prec), do: {:ok, left, rest}

  defp atom([{:num, n} | rest]), do: {:ok, {:num, n}, rest}
  defp atom([{:ident, name} | rest]), do: {:ok, {:var, name}, rest}

  defp atom([{:lparen, _} | rest]) do
    with {:ok, inner, rest2} <- expr(rest, 0),
         {:ok, rest3} <- expect(rest2, :rparen) do
      {:ok, inner, rest3}
    end
  end

  defp atom(other), do: {:error, {:unexpected_token, other}}

  defp expect_ident([{:ident, _} = tok | rest]), do: {:ok, tok, rest}
  defp expect_ident(tokens), do: {:error, {:expected_ident, tokens}}

  defp expect([{type, _} | rest], type), do: {:ok, rest}
  defp expect(tokens, type), do: {:error, {:expected, type, tokens}}

  defp expect_kw([{:kw, kw} | rest], kw), do: {:ok, rest}
  defp expect_kw(tokens, kw), do: {:error, {:expected_kw, kw, tokens}}

  defp precedence(:+), do: 10
  defp precedence(:-), do: 10
  defp precedence(:*), do: 20
  defp precedence(:/), do: 20

  # -- Evaluator -------------------------------------------------------------

  defp evaluate({:num, n}, _env), do: {:ok, n}

  defp evaluate({:var, name}, env) do
    case Map.fetch(env, name) do
      {:ok, v} -> {:ok, v}
      :error -> {:error, :undefined_variable}
    end
  end

  defp evaluate({:binop, op, left, right}, env) do
    with {:ok, l} <- evaluate(left, env),
         {:ok, r} <- evaluate(right, env) do
      apply_op(op, l, r)
    end
  end

  defp evaluate({:let, name, value, body}, env) do
    with {:ok, v} <- evaluate(value, env) do
      evaluate(body, Map.put(env, name, v))
    end
  end

  defp evaluate({:if, cond_ast, t, e}, env) do
    with {:ok, v} <- evaluate(cond_ast, env) do
      if v != 0, do: evaluate(t, env), else: evaluate(e, env)
    end
  end

  defp apply_op(:+, l, r), do: {:ok, l + r}
  defp apply_op(:-, l, r), do: {:ok, l - r}
  defp apply_op(:*, l, r), do: {:ok, l * r}

  defp apply_op(:/, _l, 0), do: {:error, :division_by_zero}
  defp apply_op(:/, l, r), do: {:ok, div(l, r)}
end
