defmodule Cure.SMT.Translator do
  @moduledoc """
  Translates Cure MetaAST constraint expressions to SMT-LIB2 format.

  Handles the MetaAST 3-tuple format from `Cure.Compiler.Parser`:
  - `{:binary_op, [operator: :+], [left, right]}` -> `(+ left right)`
  - `{:literal, [subtype: :integer], 42}` -> `42`
  - `{:variable, _, "x"}` -> `x`

  ## Usage

      ast = {:binary_op, [operator: :>], [{:variable, [], "x"}, {:literal, [subtype: :integer], 0}]}
      smt = Cure.SMT.Translator.translate(ast)
      # => "(> x 0)"
  """

  # -- Public API --------------------------------------------------------------

  @doc """
  Translate a MetaAST expression to an SMT-LIB2 s-expression string.
  """
  @spec translate(tuple()) :: String.t()
  def translate(ast), do: IO.iodata_to_binary(do_translate(ast))

  @doc """
  Generate a complete SMT-LIB2 query from a constraint AST.

  Includes logic declaration, variable declarations, assertion, and check-sat.
  """
  @spec generate_query(tuple(), map()) :: String.t()
  def generate_query(constraint_ast, var_types \\ %{}) do
    vars = collect_variables(constraint_ast)
    logic = infer_logic(constraint_ast)

    query = [
      "(set-logic #{logic})\n",
      Enum.map(vars, fn v -> declare_var(v, Map.get(var_types, v, :int)) end),
      "(assert ",
      do_translate(constraint_ast),
      ")\n",
      "(check-sat)\n"
    ]

    IO.iodata_to_binary(query)
  end

  @doc """
  Generate a refinement subtype query.

  To prove `{x: T | P1(x)} <: {x: T | P2(x)}`, we check whether
  `not (forall x. P1(x) => P2(x))` is unsatisfiable.
  If unsat, the subtyping holds.
  """
  @spec generate_subtype_query(tuple(), tuple(), String.t(), atom()) :: String.t()
  def generate_subtype_query(pred1, pred2, var_name, base_type) do
    smt_type = cure_type_to_smt(base_type)

    query = [
      "(set-logic QF_LIA)\n",
      "(declare-const #{var_name} #{smt_type})\n",
      # Assert negation of implication: not (P1 => P2)
      # i.e., P1 and not P2
      "(assert (and ",
      do_translate(pred1),
      " (not ",
      do_translate(pred2),
      ")))\n",
      "(check-sat)\n"
    ]

    IO.iodata_to_binary(query)
  end

  @doc """
  Generate a constraint satisfiability query for a single predicate.
  """
  @spec generate_constraint_query(tuple(), String.t(), atom()) :: String.t()
  def generate_constraint_query(predicate, var_name, base_type) do
    smt_type = cure_type_to_smt(base_type)

    query = [
      "(set-logic QF_LIA)\n",
      "(declare-const #{var_name} #{smt_type})\n",
      "(assert ",
      do_translate(predicate),
      ")\n",
      "(check-sat)\n"
    ]

    IO.iodata_to_binary(query)
  end

  # -- Translation Engine ------------------------------------------------------

  # Binary operators -- arithmetic
  defp do_translate({:binary_op, meta, [left, right]}) do
    op = Keyword.get(meta, :operator)
    smt_op = translate_op(op)
    ["(", smt_op, " ", do_translate(left), " ", do_translate(right), ")"]
  end

  # Unary operators
  defp do_translate({:unary_op, meta, [operand]}) do
    op = Keyword.get(meta, :operator)
    smt_op = translate_op(op)
    ["(", smt_op, " ", do_translate(operand), ")"]
  end

  # Literals
  defp do_translate({:literal, meta, value}) do
    case Keyword.get(meta, :subtype) do
      :integer -> Integer.to_string(value)
      :float -> Float.to_string(value)
      :boolean -> if value, do: "true", else: "false"
      _ -> inspect(value)
    end
  end

  # Variables
  defp do_translate({:variable, _meta, name}) when is_binary(name) do
    name
  end

  # Function calls (SMT built-ins)
  defp do_translate({:function_call, meta, args}) do
    name = Keyword.get(meta, :name, "unknown")
    translated_args = Enum.map(args, &do_translate/1)

    case name do
      "abs" ->
        ["(abs ", Enum.join(translated_args, " "), ")"]

      "min" ->
        [
          "(ite (< ",
          Enum.at(translated_args, 0),
          " ",
          Enum.at(translated_args, 1),
          ") ",
          Enum.at(translated_args, 0),
          " ",
          Enum.at(translated_args, 1),
          ")"
        ]

      "max" ->
        [
          "(ite (> ",
          Enum.at(translated_args, 0),
          " ",
          Enum.at(translated_args, 1),
          ") ",
          Enum.at(translated_args, 0),
          " ",
          Enum.at(translated_args, 1),
          ")"
        ]

      _ ->
        ["(; unknown: #{name} ;)"]
    end
  end

  # Conditional: if c then a else b -> (ite c a b)
  defp do_translate({:conditional, _meta, [cond_ast, then_ast, else_ast]}) do
    ["(ite ", do_translate(cond_ast), " ", do_translate(then_ast), " ", do_translate(else_ast), ")"]
  end

  # Fallback -- emit SMT comment and log warning; return "true" to keep query valid
  defp do_translate(ast) do
    tag =
      if is_tuple(ast) and tuple_size(ast) >= 1,
        do: Atom.to_string(elem(ast, 0)),
        else: "unknown"

    require Logger
    Logger.warning("SMT translator: untranslatable AST node '#{tag}', approximated as true")

    ["(; untranslatable: #{tag} ;) true"]
  end

  # -- Operator Mapping --------------------------------------------------------

  defp translate_op(:+), do: "+"
  defp translate_op(:-), do: "-"
  defp translate_op(:*), do: "*"
  defp translate_op(:/), do: "div"
  defp translate_op(:%), do: "mod"
  defp translate_op(:==), do: "="
  defp translate_op(:!=), do: "distinct"
  defp translate_op(:<), do: "<"
  defp translate_op(:>), do: ">"
  defp translate_op(:<=), do: "<="
  defp translate_op(:>=), do: ">="
  defp translate_op(:and), do: "and"
  defp translate_op(:or), do: "or"
  defp translate_op(:not), do: "not"
  defp translate_op(op), do: Atom.to_string(op)

  # -- Variable Collection -----------------------------------------------------

  @doc "Collect all variable names from a constraint AST."
  @spec collect_variables(tuple()) :: [String.t()]
  def collect_variables(ast) do
    ast |> do_collect_vars([]) |> Enum.uniq() |> Enum.sort()
  end

  defp do_collect_vars({:variable, _meta, name}, acc), do: [name | acc]

  defp do_collect_vars({:binary_op, _meta, [left, right]}, acc) do
    acc = do_collect_vars(left, acc)
    do_collect_vars(right, acc)
  end

  defp do_collect_vars({:unary_op, _meta, [operand]}, acc) do
    do_collect_vars(operand, acc)
  end

  defp do_collect_vars({:function_call, _meta, args}, acc) do
    Enum.reduce(args, acc, &do_collect_vars/2)
  end

  defp do_collect_vars(_ast, acc), do: acc

  # -- Logic Inference ---------------------------------------------------------

  defp infer_logic(ast) do
    features = analyze_features(ast, %{has_nonlinear: false, has_floats: false})

    cond do
      features.has_floats and features.has_nonlinear -> "QF_NRA"
      features.has_floats -> "QF_LRA"
      features.has_nonlinear -> "QF_NIA"
      true -> "QF_LIA"
    end
  end

  defp analyze_features({:binary_op, meta, [left, right]}, acc) do
    op = Keyword.get(meta, :operator)
    acc = if op in [:*, :/], do: %{acc | has_nonlinear: true}, else: acc
    acc = analyze_features(left, acc)
    analyze_features(right, acc)
  end

  defp analyze_features({:literal, meta, _}, acc) do
    if Keyword.get(meta, :subtype) == :float, do: %{acc | has_floats: true}, else: acc
  end

  defp analyze_features(_, acc), do: acc

  # -- Type Mapping ------------------------------------------------------------

  defp cure_type_to_smt(:int), do: "Int"
  defp cure_type_to_smt(:float), do: "Real"
  defp cure_type_to_smt(:bool), do: "Bool"
  defp cure_type_to_smt(:nat), do: "Int"
  defp cure_type_to_smt(_), do: "Int"

  defp declare_var(name, type) do
    "(declare-const #{name} #{cure_type_to_smt(type)})\n"
  end
end
