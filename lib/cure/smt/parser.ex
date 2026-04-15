defmodule Cure.SMT.Parser do
  @moduledoc """
  Parses Z3 S-expression output into Elixir data structures.

  Used to extract counterexample models from `(get-model)` output.

  ## Example

      output = \"\"\"
      (model
        (define-fun x () Int 42)
        (define-fun y () Int -3))
      \"\"\"

      {:ok, model} = Cure.SMT.Parser.parse_model(output)
      # => %{"x" => 42, "y" => -3}
  """

  @doc """
  Parse a Z3 model output string into a variable -> value map.
  """
  @spec parse_model(String.t()) :: {:ok, map()} | {:error, term()}
  def parse_model(output) do
    # Extract define-fun entries
    entries =
      Regex.scan(~r/\(define-fun\s+(\w+)\s+\(\)\s+\w+\s+([^\)]+)\)/, output)
      |> Enum.map(fn [_full, name, value_str] ->
        {name, parse_value(String.trim(value_str))}
      end)
      |> Map.new()

    {:ok, entries}
  rescue
    _ -> {:error, :parse_failed}
  end

  @doc """
  Parse a Z3 S-expression string into a nested list/atom structure.
  """
  @spec parse_sexp(String.t()) :: {:ok, term()} | {:error, term()}
  def parse_sexp(input) do
    tokens = tokenize(String.trim(input))

    case parse_tokens(tokens) do
      {result, []} -> {:ok, result}
      {result, _rest} -> {:ok, result}
    end
  rescue
    _ -> {:error, :parse_failed}
  end

  # -- Value Parsing -----------------------------------------------------------

  defp parse_value(str) do
    cond do
      str =~ ~r/^-?\d+$/ ->
        String.to_integer(str)

      str =~ ~r/^-?\d+\.\d+$/ ->
        String.to_float(str)

      str == "true" ->
        true

      str == "false" ->
        false

      # Negative number in S-expression: (- 42)
      str =~ ~r/^\(-\s*\d+\)$/ ->
        [_, n] = Regex.run(~r/\(-\s*(\d+)\)/, str)
        -String.to_integer(n)

      true ->
        str
    end
  end

  # -- S-expression Tokenizer --------------------------------------------------

  defp tokenize(input) do
    input
    |> String.replace("(", " ( ")
    |> String.replace(")", " ) ")
    |> String.split(~r/\s+/, trim: true)
  end

  # -- S-expression Parser -----------------------------------------------------

  defp parse_tokens(["(" | rest]) do
    parse_list(rest, [])
  end

  defp parse_tokens([token | rest]) do
    {parse_atom(token), rest}
  end

  defp parse_tokens([]) do
    {nil, []}
  end

  defp parse_list([")" | rest], acc) do
    {Enum.reverse(acc), rest}
  end

  defp parse_list(tokens, acc) do
    {item, rest} = parse_tokens(tokens)
    parse_list(rest, [item | acc])
  end

  defp parse_atom(str) do
    cond do
      str =~ ~r/^-?\d+$/ -> String.to_integer(str)
      str =~ ~r/^-?\d+\.\d+$/ -> String.to_float(str)
      true -> str
    end
  end
end
