defmodule Cure.Compiler.Printer do
  @moduledoc """
  Converts a MetaAST tree back into Cure source code.

  This is the inverse of `Cure.Compiler.Parser`. Given a well-formed MetaAST
  (the `{type, keyword_meta, children_or_value}` 3-tuples produced by the
  parser), it emits a Cure source string that round-trips through the
  lexer/parser pipeline.

  ## Options

  - `:indent` -- indentation unit (default: `"  "`)
  """

  @default_indent "  "

  @doc """
  Render a MetaAST node as a Cure source string.
  """
  @spec quoted_to_string(term(), keyword()) :: String.t()
  def quoted_to_string(ast, opts \\ []) do
    indent = Keyword.get(opts, :indent, @default_indent)
    to_string(ast, 0, indent)
  end

  # -- Literals --------------------------------------------------------------

  defp to_string({:literal, meta, value}, _depth, _indent) do
    case Keyword.get(meta, :subtype) do
      :integer -> Integer.to_string(value)
      :float -> float_to_string(value)
      :string -> ~s("#{escape_string(value)}")
      :boolean -> Atom.to_string(value)
      :null -> "nil"
      :symbol -> ":#{value}"
      :regex -> regex_to_string(value)
      :char -> char_to_string(value)
      :bytes -> bytes_to_string(meta, value)
      _ -> inspect(value)
    end
  end

  # -- Variables -------------------------------------------------------------

  defp to_string({:variable, _meta, name}, _depth, _indent), do: name

  # -- Block -----------------------------------------------------------------

  defp to_string({:block, _meta, exprs}, depth, indent) do
    exprs
    |> Enum.map(&to_string(&1, depth, indent))
    |> Enum.join("\n" <> String.duplicate(indent, depth))
  end

  # -- Binary Operators ------------------------------------------------------

  defp to_string({:binary_op, meta, [left, right]}, depth, indent) do
    op = Keyword.get(meta, :operator)
    op_str = operator_to_string(op)
    "#{to_string(left, depth, indent)} #{op_str} #{to_string(right, depth, indent)}"
  end

  # -- Unary Operators -------------------------------------------------------

  defp to_string({:unary_op, meta, [operand]}, depth, indent) do
    op = Keyword.get(meta, :operator)

    case op do
      :not -> "not #{to_string(operand, depth, indent)}"
      :- -> "-#{to_string(operand, depth, indent)}"
      _ -> "#{op}#{to_string(operand, depth, indent)}"
    end
  end

  # -- Assignment (let binding) -----------------------------------------------

  defp to_string({:assignment, meta, [pattern, value]}, depth, indent) do
    type_ann =
      case Keyword.get(meta, :type_annotation) do
        nil -> ""
        type_ast -> ": #{to_string(type_ast, depth, indent)}"
      end

    lhs = to_string(pattern, depth, indent)
    rhs = rhs_to_string(value, depth, indent)

    if Keyword.get(meta, :let) do
      "let #{lhs}#{type_ann} = #{rhs}"
    else
      "#{lhs} = #{rhs}"
    end
  end

  # -- Augmented Assignment --------------------------------------------------

  defp to_string({:augmented_assignment, meta, [lhs, rhs]}, depth, indent) do
    op = Keyword.get(meta, :operator)

    op_str =
      case op do
        :+ -> "+="
        :- -> "-="
        :* -> "*="
        :/ -> "/="
      end

    "#{to_string(lhs, depth, indent)} #{op_str} #{to_string(rhs, depth, indent)}"
  end

  # -- Conditional -----------------------------------------------------------

  defp to_string({:conditional, _meta, [condition, then_br, else_br]}, depth, indent) do
    cond_str = to_string(condition, depth, indent)

    case {then_br, else_br} do
      {_, {:literal, [subtype: :null], nil}} ->
        # No else branch
        "if #{cond_str} then #{to_string(then_br, depth, indent)}"

      {_, {:conditional, _, _}} ->
        # elif chain
        then_str = to_string(then_br, depth, indent)
        elif_str = conditional_to_elif(else_br, depth, indent)
        "if #{cond_str} then #{then_str} #{elif_str}"

      _ ->
        then_str = to_string(then_br, depth, indent)
        else_str = to_string(else_br, depth, indent)
        "if #{cond_str} then #{then_str} else #{else_str}"
    end
  end

  # -- Pattern Match ---------------------------------------------------------

  defp to_string({:pattern_match, _meta, [scrutinee | arms]}, depth, indent) do
    scrut_str = to_string(scrutinee, depth, indent)

    arms_str =
      arms
      |> Enum.map(&match_arm_to_string(&1, depth, indent))
      |> Enum.join(", ")

    "match #{scrut_str} { #{arms_str} }"
  end

  # -- Match Arm -------------------------------------------------------------

  defp to_string({:match_arm, meta, [body]}, depth, indent) do
    match_arm_to_string({:match_arm, meta, [body]}, depth, indent)
  end

  # -- Function Call ---------------------------------------------------------

  defp to_string({:function_call, meta, args}, depth, indent) do
    name = Keyword.get(meta, :name, "unknown")

    cond do
      # Record construction: Name{field: val}
      Keyword.get(meta, :record) == true ->
        fields_str = pairs_to_string(args, depth, indent)
        "#{name}{#{fields_str}}"

      # Send: send target, message
      name == "send" and not Keyword.has_key?(meta, :pipe) ->
        case args do
          [target, message] ->
            "send #{to_string(target, depth, indent)}, #{to_string(message, depth, indent)}"

          _ ->
            "#{name}(#{args_to_string(args, depth, indent)})"
        end

      # FSM transition
      Keyword.get(meta, :from) != nil ->
        fsm_transition_to_string(meta, depth, indent)

      # Pipe call
      Keyword.get(meta, :pipe) == true ->
        case args do
          [piped | rest] when rest != [] ->
            "#{to_string(piped, depth, indent)} |> #{name}(#{args_to_string(rest, depth, indent)})"

          [piped] ->
            "#{to_string(piped, depth, indent)} |> #{name}"

          [] ->
            name
        end

      true ->
        "#{name}(#{args_to_string(args, depth, indent)})"
    end
  end

  # -- Attribute Access (dot) ------------------------------------------------

  defp to_string({:attribute_access, meta, [parent]}, depth, indent) do
    attr = Keyword.get(meta, :attribute)
    "#{to_string(parent, depth, indent)}.#{attr}"
  end

  # -- Range -----------------------------------------------------------------

  defp to_string({:range, meta, [left, right]}, depth, indent) do
    op = if Keyword.get(meta, :inclusive), do: "..=", else: ".."
    "#{to_string(left, depth, indent)}#{op}#{to_string(right, depth, indent)}"
  end

  # -- Collections -----------------------------------------------------------

  defp to_string({:list, meta, elements}, depth, indent) do
    if Keyword.get(meta, :cons) do
      case elements do
        [head, tail] ->
          "[#{to_string(head, depth, indent)} | #{to_string(tail, depth, indent)}]"

        _ ->
          "[#{args_to_string(elements, depth, indent)}]"
      end
    else
      "[#{args_to_string(elements, depth, indent)}]"
    end
  end

  defp to_string({:tuple, _meta, elements}, depth, indent) do
    "%[#{args_to_string(elements, depth, indent)}]"
  end

  defp to_string({:map, _meta, pairs}, depth, indent) do
    "%{#{pairs_to_string(pairs, depth, indent)}}"
  end

  defp to_string({:pair, _meta, [key, value]}, depth, indent) do
    pair_to_string(key, value, depth, indent)
  end

  # -- Comprehension ---------------------------------------------------------

  defp to_string({:comprehension, _meta, [body | generators_and_filters]}, depth, indent) do
    body_str = to_string(body, depth, indent)
    clauses = Enum.map(generators_and_filters, &gen_or_filter_to_string(&1, depth, indent))
    "[#{body_str} for #{Enum.join(clauses, ", ")}]"
  end

  defp to_string({:generator, _meta, [pattern, collection]}, depth, indent) do
    gen_or_filter_to_string({:generator, [], [pattern, collection]}, depth, indent)
  end

  defp to_string({:filter, _meta, [expr]}, depth, indent) do
    gen_or_filter_to_string({:filter, [], [expr]}, depth, indent)
  end

  # -- String Interpolation --------------------------------------------------

  defp to_string({:string_interpolation, _meta, parts}, depth, indent) do
    inner =
      Enum.map_join(parts, fn
        {:literal, [subtype: :string], s} -> escape_string(s)
        {:literal, _, s} when is_binary(s) -> escape_string(s)
        expr -> "\#{#{to_string(expr, depth, indent)}}"
      end)

    ~s("#{inner}")
  end

  # -- Lambda ----------------------------------------------------------------

  defp to_string({:lambda, meta, [body]}, depth, indent) do
    params = Keyword.get(meta, :params, [])
    params_str = Enum.map_join(params, ", ", fn {:param, _, name} -> name end)
    "fn(#{params_str}) -> #{to_string(body, depth, indent)}"
  end

  # -- Function Definition ---------------------------------------------------

  defp to_string({:function_def, meta, body}, depth, indent) do
    fn_def_to_string(meta, body, depth, indent)
  end

  # -- Container (module, record, enum, protocol, trait, fsm) ----------------

  defp to_string({:container, meta, body}, depth, indent) do
    container_to_string(meta, body, depth, indent)
  end

  # -- Type Annotation -------------------------------------------------------

  defp to_string({:type_annotation, meta, children}, depth, indent) do
    type_annotation_to_string(meta, children, depth, indent)
  end

  # -- Import ----------------------------------------------------------------

  defp to_string({:import, meta, _children}, _depth, _indent) do
    source = Keyword.get(meta, :source)
    items = Keyword.get(meta, :items)
    alias_name = Keyword.get(meta, :alias)

    base = "use #{source}"

    base =
      if items && items != [] do
        base <> ".{#{Enum.join(items, ", ")}}"
      else
        base
      end

    if alias_name do
      base <> " as #{alias_name}"
    else
      base
    end
  end

  # -- Early Return / Throw / Yield / Spawn ---------------------------------

  defp to_string({:early_return, _meta, [expr]}, depth, indent) do
    "return #{to_string(expr, depth, indent)}"
  end

  defp to_string({:throw, _meta, [expr]}, depth, indent) do
    "throw #{to_string(expr, depth, indent)}"
  end

  defp to_string({:yield, _meta, [expr]}, depth, indent) do
    "yield #{to_string(expr, depth, indent)}"
  end

  defp to_string({:async_operation, meta, children}, depth, indent) do
    case Keyword.get(meta, :timeout) do
      nil when children == [] ->
        "receive"

      nil ->
        arms_str =
          children
          |> Enum.map(&match_arm_to_string(&1, depth + 1, indent))
          |> Enum.join("\n" <> String.duplicate(indent, depth + 1))

        pad = String.duplicate(indent, depth + 1)
        "receive\n#{pad}#{arms_str}"

      _ ->
        # receive with timeout
        arms_str =
          children
          |> Enum.map(&match_arm_to_string(&1, depth + 1, indent))
          |> Enum.join("\n" <> String.duplicate(indent, depth + 1))

        pad = String.duplicate(indent, depth + 1)
        "receive\n#{pad}#{arms_str}"
    end
  end

  # -- Exception Handling ----------------------------------------------------

  defp to_string({:exception_handling, _meta, children}, depth, indent) do
    pad = String.duplicate(indent, depth + 1)

    case children do
      [try_body | rest] ->
        try_str = "try\n#{pad}#{to_string(try_body, depth + 1, indent)}"

        {catch_arms, rest} =
          Enum.split_while(rest, fn
            {:match_arm, _, _} -> true
            _ -> false
          end)

        catch_str =
          if catch_arms != [] do
            arms =
              catch_arms
              |> Enum.map(&match_arm_to_string(&1, depth + 1, indent))
              |> Enum.join("\n#{pad}")

            "\ncatch\n#{pad}#{arms}"
          else
            ""
          end

        finally_str =
          case rest do
            [finally_body] ->
              "\nfinally\n#{pad}#{to_string(finally_body, depth + 1, indent)}"

            _ ->
              ""
          end

        "#{try_str}#{catch_str}#{finally_str}"

      _ ->
        "try"
    end
  end

  # -- Decorator / Property --------------------------------------------------

  defp to_string({:decorator, meta, args}, depth, indent) do
    name = Keyword.get(meta, :name)
    "@#{name}(#{args_to_string(args, depth, indent)})"
  end

  defp to_string({:property, meta, _value}, _depth, _indent) do
    name = Keyword.get(meta, :name)
    "@#{name}"
  end

  # -- Fallback --------------------------------------------------------------

  defp to_string(other, _depth, _indent) when is_binary(other), do: other

  defp to_string(other, _depth, _indent) do
    inspect(other)
  end

  # ── Helpers ──────────────────────────────────────────────────────────────

  defp operator_to_string(:+), do: "+"
  defp operator_to_string(:-), do: "-"
  defp operator_to_string(:*), do: "*"
  defp operator_to_string(:/), do: "/"
  defp operator_to_string(:rem), do: "%"
  defp operator_to_string(:==), do: "=="
  defp operator_to_string(:!=), do: "!="
  defp operator_to_string(:<), do: "<"
  defp operator_to_string(:>), do: ">"
  defp operator_to_string(:<=), do: "<="
  defp operator_to_string(:>=), do: ">="
  defp operator_to_string(:and), do: "and"
  defp operator_to_string(:or), do: "or"
  defp operator_to_string(:<>), do: "<>"
  defp operator_to_string(:..), do: ".."
  defp operator_to_string(:"..="), do: "..="
  defp operator_to_string(:|>), do: "|>"
  defp operator_to_string(:.), do: "."
  defp operator_to_string(:=), do: "="
  defp operator_to_string(other), do: Atom.to_string(other)

  defp args_to_string(args, depth, indent) do
    Enum.map_join(args, ", ", &to_string(&1, depth, indent))
  end

  defp pairs_to_string(pairs, depth, indent) do
    Enum.map_join(pairs, ", ", &to_string(&1, depth, indent))
  end

  defp pair_to_string(key, value, depth, indent) do
    case key do
      {:literal, [subtype: :symbol], atom_val} when is_atom(atom_val) ->
        "#{atom_val}: #{to_string(value, depth, indent)}"

      _ ->
        "#{to_string(key, depth, indent)} => #{to_string(value, depth, indent)}"
    end
  end

  defp match_arm_to_string({:match_arm, meta, [body]}, depth, indent) do
    pattern = Keyword.get(meta, :pattern)
    guard = Keyword.get(meta, :guard)
    pat_str = to_string(pattern, depth, indent)
    body_str = to_string(body, depth, indent)

    if guard do
      "#{pat_str} when #{to_string(guard, depth, indent)} -> #{body_str}"
    else
      "#{pat_str} -> #{body_str}"
    end
  end

  defp gen_or_filter_to_string({:generator, _meta, [pattern, collection]}, depth, indent) do
    "#{to_string(pattern, depth, indent)} <- #{to_string(collection, depth, indent)}"
  end

  defp gen_or_filter_to_string({:filter, _meta, [expr]}, depth, indent) do
    to_string(expr, depth, indent)
  end

  defp conditional_to_elif({:conditional, _meta, [cond_ast, then_br, else_br]}, depth, indent) do
    cond_str = to_string(cond_ast, depth, indent)
    then_str = to_string(then_br, depth, indent)

    case else_br do
      {:literal, [subtype: :null], nil} ->
        "elif #{cond_str} then #{then_str}"

      {:conditional, _, _} ->
        "elif #{cond_str} then #{then_str} #{conditional_to_elif(else_br, depth, indent)}"

      _ ->
        "elif #{cond_str} then #{then_str} else #{to_string(else_br, depth, indent)}"
    end
  end

  defp rhs_to_string({:block, _meta, exprs}, depth, indent) do
    pad = String.duplicate(indent, depth + 1)

    inner =
      exprs
      |> Enum.map(&to_string(&1, depth + 1, indent))
      |> Enum.join("\n#{pad}")

    "\n#{pad}#{inner}"
  end

  defp rhs_to_string(ast, depth, indent), do: to_string(ast, depth, indent)

  # -- Function Definition ---------------------------------------------------

  defp fn_def_to_string(meta, body, depth, indent) do
    name = Keyword.get(meta, :name)
    visibility = Keyword.get(meta, :visibility, :public)
    params = Keyword.get(meta, :params, [])
    return_type = Keyword.get(meta, :return_type)
    guard = Keyword.get(meta, :guards)
    constraints = Keyword.get(meta, :constraints, [])
    clauses = Keyword.get(meta, :clauses)
    extern = Keyword.get(meta, :extern)
    decorator = Keyword.get(meta, :decorator)

    prefix = if visibility == :private, do: "local fn", else: "fn"
    params_str = typed_params_to_string(params, depth, indent)
    ret_str = if return_type, do: " -> #{to_string(return_type, depth, indent)}", else: ""

    guard_str =
      if guard, do: " when #{to_string(guard, depth, indent)}", else: ""

    constraints_str =
      if constraints != [] do
        cs = Enum.map_join(constraints, ", ", &to_string(&1, depth, indent))
        " where #{cs}"
      else
        ""
      end

    sig = "#{prefix} #{name}(#{params_str})#{ret_str}#{guard_str}#{constraints_str}"

    result =
      cond do
        clauses != nil and clauses != [] ->
          pad = String.duplicate(indent, depth + 1)

          clauses_str =
            clauses
            |> Enum.map(&fn_clause_to_string(&1, depth + 1, indent))
            |> Enum.join("\n#{pad}")

          "#{sig}\n#{pad}#{clauses_str}"

        body == [] ->
          # Signature only (protocol)
          sig

        true ->
          [body_ast] = body
          "#{sig} = #{rhs_to_string(body_ast, depth, indent)}"
      end

    result = maybe_prepend_decorator(result, extern, decorator, depth, indent)
    result
  end

  defp maybe_prepend_decorator(result, nil, nil, _depth, _indent), do: result

  defp maybe_prepend_decorator(result, extern, _decorator, _depth, _indent) when extern != nil do
    {m, f, a} =
      case extern do
        {m, f, a} -> {m, f, a}
        _ -> {nil, nil, nil}
      end

    if m do
      "@extern(:#{m}, :#{f}, #{a})\n#{result}"
    else
      result
    end
  end

  defp maybe_prepend_decorator(result, _extern, {dec_name, args}, depth, indent) do
    args_str =
      if args != [] do
        "(#{args_to_string(args, depth, indent)})"
      else
        ""
      end

    "@#{dec_name}#{args_str}\n#{result}"
  end

  defp maybe_prepend_decorator(result, _, _, _, _), do: result

  defp typed_params_to_string(params, depth, indent) do
    Enum.map_join(params, ", ", fn {:param, meta, name} ->
      kind = Keyword.get(meta, :kind)
      type_ast = Keyword.get(meta, :type)
      default = Keyword.get(meta, :default)

      prefix =
        case kind do
          :variadic -> "*"
          :keyword_variadic -> "**"
          _ -> ""
        end

      type_str = if type_ast, do: ": #{to_string(type_ast, depth, indent)}", else: ""
      default_str = if default, do: " = #{to_string(default, depth, indent)}", else: ""
      "#{prefix}#{name}#{type_str}#{default_str}"
    end)
  end

  defp fn_clause_to_string(%{params: params, guard: guard, body: [body_ast]}, depth, indent) do
    params_str = Enum.map_join(params, ", ", &to_string(&1, depth, indent))
    guard_str = if guard, do: " when #{to_string(guard, depth, indent)}", else: ""
    body_str = to_string(body_ast, depth, indent)
    "| #{params_str}#{guard_str} -> #{body_str}"
  end

  # -- Container -------------------------------------------------------------

  defp container_to_string(meta, body, depth, indent) do
    type = Keyword.get(meta, :container_type)

    case type do
      :module -> module_to_string(meta, body, depth, indent)
      :struct -> record_to_string(meta, body, depth, indent)
      :enum -> enum_to_string(meta, body, depth, indent)
      :protocol -> protocol_to_string(meta, body, depth, indent)
      :trait -> impl_to_string(meta, body, depth, indent)
      :fsm -> fsm_to_string(meta, body, depth, indent)
      _ -> inspect({:container, meta, body})
    end
  end

  defp module_to_string(meta, body, depth, indent) do
    name = Keyword.get(meta, :name)
    pad = String.duplicate(indent, depth + 1)

    body_str =
      body
      |> Enum.map(&to_string(&1, depth + 1, indent))
      |> Enum.join("\n#{pad}")

    "mod #{name}\n#{pad}#{body_str}"
  end

  defp record_to_string(meta, fields, depth, indent) do
    name = Keyword.get(meta, :name)
    type_params = Keyword.get(meta, :type_params)
    pad = String.duplicate(indent, depth + 1)

    tp_str =
      if type_params && type_params != [] do
        "(#{Enum.join(type_params, ", ")})"
      else
        ""
      end

    fields_str =
      fields
      |> Enum.map(fn {:param, field_meta, field_name} ->
        type_ast = Keyword.get(field_meta, :type)
        "#{field_name}: #{to_string(type_ast, depth + 1, indent)}"
      end)
      |> Enum.join("\n#{pad}")

    "rec #{name}#{tp_str}\n#{pad}#{fields_str}"
  end

  defp enum_to_string(meta, variants, depth, indent) do
    name = Keyword.get(meta, :name)
    type_params = Keyword.get(meta, :type_params)

    tp_str =
      if type_params && type_params != [] do
        "(#{Enum.join(type_params, ", ")})"
      else
        ""
      end

    variants_str =
      variants
      |> Enum.map(&variant_to_string(&1, depth, indent))
      |> Enum.join(" | ")

    "type #{name}#{tp_str} = #{variants_str}"
  end

  defp variant_to_string({:function_def, meta, []}, depth, indent) do
    name = Keyword.get(meta, :name)
    params = Keyword.get(meta, :params, [])

    if params != [] do
      params_str = Enum.map_join(params, ", ", &to_string(&1, depth, indent))
      "#{name}(#{params_str})"
    else
      name
    end
  end

  defp variant_to_string({:variable, _meta, name}, _depth, _indent), do: name
  defp variant_to_string(other, depth, indent), do: to_string(other, depth, indent)

  defp protocol_to_string(meta, body, depth, indent) do
    name = Keyword.get(meta, :name)
    type_params = Keyword.get(meta, :type_params, [])
    pad = String.duplicate(indent, depth + 1)

    tp_str =
      if type_params != [] do
        "(#{Enum.join(type_params, ", ")})"
      else
        ""
      end

    body_str =
      body
      |> Enum.map(&to_string(&1, depth + 1, indent))
      |> Enum.join("\n#{pad}")

    "proto #{name}#{tp_str}\n#{pad}#{body_str}"
  end

  defp impl_to_string(meta, body, depth, indent) do
    protocol = Keyword.get(meta, :protocol)
    for_type = Keyword.get(meta, :for)
    constraints = Keyword.get(meta, :constraints, [])
    pad = String.duplicate(indent, depth + 1)

    constraints_str =
      if constraints != [] do
        cs = Enum.map_join(constraints, ", ", &to_string(&1, depth, indent))
        " where #{cs}"
      else
        ""
      end

    body_str =
      body
      |> Enum.map(&to_string(&1, depth + 1, indent))
      |> Enum.join("\n#{pad}")

    "impl #{protocol} for #{for_type}#{constraints_str}\n#{pad}#{body_str}"
  end

  defp fsm_to_string(meta, body, depth, indent) do
    name = Keyword.get(meta, :name)
    payload = Keyword.get(meta, :payload)
    pad = String.duplicate(indent, depth + 1)

    payload_str =
      if payload do
        " with #{to_string(payload, depth, indent)}"
      else
        ""
      end

    transitions_str =
      body
      |> Enum.map(&to_string(&1, depth + 1, indent))
      |> Enum.join("\n#{pad}")

    "fsm #{name}#{payload_str}\n#{pad}#{transitions_str}"
  end

  defp fsm_transition_to_string(meta, _depth, _indent) do
    from = Keyword.get(meta, :from)
    event = Keyword.get(meta, :event)
    to = Keyword.get(meta, :to)
    "#{from} --#{event}--> #{to}"
  end

  # -- Type Annotation -------------------------------------------------------

  defp type_annotation_to_string(meta, children, depth, indent) do
    name = Keyword.get(meta, :name)
    type_params = Keyword.get(meta, :type_params)
    refinement = Keyword.get(meta, :refinement, false)

    tp_str =
      if type_params && type_params != [] do
        "(#{Enum.join(type_params, ", ")})"
      else
        ""
      end

    if refinement do
      case children do
        [var_ast, base_type, predicate] ->
          var_str = to_string(var_ast, depth, indent)
          base_str = to_string(base_type, depth, indent)
          pred_str = to_string(predicate, depth, indent)
          "type #{name}#{tp_str} = {#{var_str}: #{base_str} | #{pred_str}}"

        _ ->
          "type #{name}#{tp_str} = #{args_to_string(children, depth, indent)}"
      end
    else
      case children do
        [type_expr] ->
          "type #{name}#{tp_str} = #{to_string(type_expr, depth, indent)}"

        _ ->
          "type #{name}#{tp_str} = #{args_to_string(children, depth, indent)}"
      end
    end
  end

  # -- Literal helpers -------------------------------------------------------

  defp escape_string(s) when is_binary(s) do
    s
    |> String.replace("\\", "\\\\")
    |> String.replace("\"", "\\\"")
    |> String.replace("\n", "\\n")
    |> String.replace("\t", "\\t")
  end

  defp float_to_string(f) when is_float(f) do
    # Use shortest representation that round-trips correctly
    short = :erlang.float_to_binary(f, [:short])

    # Ensure it contains a dot so it parses as a float
    if String.contains?(short, ".") or String.contains?(short, "e") do
      short
    else
      short <> ".0"
    end
  end

  defp regex_to_string({body, flags}), do: "~r/#{body}/#{flags}"
  defp regex_to_string(other), do: inspect(other)

  defp char_to_string(c) when is_integer(c) do
    case c do
      ?\n -> "'\\n'"
      ?\t -> "'\\t'"
      ?\\ -> "'\\\\'"
      ?' -> "'\\''"
      0 -> "'\\0'"
      _ -> "'#{<<c::utf8>>}'"
    end
  end

  defp bytes_to_string(_meta, elements) when is_list(elements) do
    if elements == [] do
      "<<>>"
    else
      inner = Enum.map_join(elements, ", ", &to_string(&1, 0, @default_indent))
      "<<#{inner}>>"
    end
  end

  defp bytes_to_string(_meta, _value), do: "<<>>"
end
