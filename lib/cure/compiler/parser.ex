defmodule Cure.Compiler.Parser do
  @moduledoc """
  Pratt parser for the Cure programming language.

  Transforms a token list from `Cure.Compiler.Lexer` into a MetaAST tree
  using Metastatic's 3-tuple format `{type, keyword_meta, children_or_value}`.

  The parser is indentation-aware: `:indent`/`:dedent`/`:newline` tokens from
  the lexer drive block structure.

  ## Record syntax

  Two record syntactic forms share the same `TypeName{...}` opening:

  - **Construction** `Point{x: 1, y: 2}` -- emits
    `{:function_call, [name: "Point", record: true, ...], field_pairs}`
  - **Update** `Point{p | x: 1}` -- emits
    `{:record_update, [name: "Point", ...], [base_expr | field_pairs]}`

  Detection uses a probe: after consuming `{`, one expression is parsed and
  the next token is inspected. If it is `|`, the parser commits to update
  mode. Otherwise it rewinds (saves and restores `pos` and `errors`) and
  falls back to normal field-pair parsing.

  ## Pipeline Events

  Emits via `Cure.Pipeline.Events`:

  - `{:parser, :node_parsed, ast, meta}` -- after each top-level expression
  - `{:parser, :parse_complete, ast, meta}` -- when parsing finishes
  - `{:parser, :error, error, meta}` -- on parse errors

  ## Usage

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(source)
      {:ok, ast} = Cure.Compiler.Parser.parse(tokens)
  """

  alias Cure.Compiler.Token
  alias Cure.Compiler.Parser.Precedence
  alias Cure.Pipeline.Events

  # -- Parser State ----------------------------------------------------------

  defstruct [:tokens, :file, pos: 0, errors: [], emit_events: false]

  @type t :: %__MODULE__{}
  @type ast :: {atom(), keyword(), term()}
  @type result :: {ast(), t()}

  # -- Public API ------------------------------------------------------------

  @doc """
  Parse a token list into a MetaAST.

  Returns `{:ok, ast}` on success or `{:error, errors}` on failure.
  If the source contains multiple top-level expressions, they are wrapped
  in a `{:block, meta, exprs}` node.

  ## Options

  - `:file` -- filename for metadata (default: `"nofile"`)
  - `:emit_events` -- whether to emit pipeline events (default: `true`)
  """
  @spec parse([Token.t()], keyword()) :: {:ok, ast()} | {:error, [term()]}
  def parse(tokens, opts \\ []) do
    file = Keyword.get(opts, :file, "nofile")
    emit? = Keyword.get(opts, :emit_events, true)
    state = %__MODULE__{tokens: tokens, file: file, emit_events: emit?}

    {exprs, state} = parse_program(state)

    ast =
      case exprs do
        [single] -> single
        many -> {:block, [line: 1, col: 1], many}
      end

    if emit? do
      Events.emit(:parser, :parse_complete, ast, Events.meta(file, 1))
    end

    case state.errors do
      [] -> {:ok, ast}
      errors -> {:error, Enum.reverse(errors)}
    end
  end

  # -- Program (top-level sequence) ------------------------------------------

  defp parse_program(state) do
    state = skip_newlines(state)
    parse_program(state, [])
  end

  defp parse_program(state, acc) do
    case peek(state) do
      %Token{type: :eof} ->
        {Enum.reverse(acc), state}

      %Token{type: :dedent} ->
        {Enum.reverse(acc), state}

      %Token{type: :doc_comment} ->
        # Collect consecutive doc comments, attach to next definition
        {doc_text, state} = collect_doc_comments(state)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: type} when type in [:eof, :dedent] ->
            {Enum.reverse(acc), state}

          _ ->
            {expr, state} = parse_expr(state, 0)
            expr = attach_doc(expr, doc_text)
            state = skip_newlines(state)
            parse_program(state, [expr | acc])
        end

      _ ->
        {expr, state} = parse_expr(state, 0)
        state = skip_newlines(state)

        if state.emit_events do
          line =
            case expr do
              {_, meta, _} when is_list(meta) -> Keyword.get(meta, :line, 1)
              _ -> 1
            end

          Events.emit(:parser, :node_parsed, expr, Events.meta(state.file, max(line, 1)))
        end

        parse_program(state, [expr | acc])
    end
  end

  # -- Core Pratt Loop -------------------------------------------------------

  defp parse_expr(state, min_bp) do
    {left, state} = parse_prefix(state)
    parse_infix(state, left, min_bp)
  end

  defp parse_infix(state, left, min_bp) do
    token = peek(state)

    cond do
      # Postfix: function call  f(...)
      token.type == :lparen and min_bp <= 110 ->
        {left, state} = parse_call(state, left)
        parse_infix(state, left, min_bp)

      # Postfix: record construction  Name{...}
      token.type == :lbrace and min_bp <= 110 and is_pascal_case?(left) ->
        {left, state} = parse_record_construction(state, left)
        parse_infix(state, left, min_bp)

      true ->
        case Precedence.infix_bp(token.type) do
          {left_bp, _right_bp} when left_bp < min_bp ->
            {left, state}

          {_left_bp, right_bp} ->
            state = advance(state)
            handle_infix_op(state, left, token, right_bp, min_bp)

          :not_infix ->
            {left, state}
        end
    end
  end

  # -- Prefix Parsing --------------------------------------------------------

  defp parse_prefix(state) do
    token = peek(state)

    case token.type do
      # Literals
      :integer ->
        {literal(:integer, token), advance(state)}

      :float ->
        {literal(:float, token), advance(state)}

      :string ->
        {literal(:string, token), advance(state)}

      :bool ->
        {literal(:boolean, token), advance(state)}

      nil ->
        {literal(:null, token), advance(state)}

      :atom ->
        {literal(:symbol, token), advance(state)}

      :regex ->
        {literal(:regex, token), advance(state)}

      :char ->
        {literal(:char, token), advance(state)}

      :string_interpolation ->
        parse_string_interpolation(state)

      # Variables / identifiers
      :identifier ->
        {variable(token), advance(state)}

      # Unary operators
      :minus ->
        parse_unary(state, :arithmetic)

      :not_op ->
        parse_unary(state, :boolean)

      # Grouping
      :lparen ->
        parse_grouped(state)

      # Collections
      :lbracket ->
        parse_list_or_comprehension(state)

      :tuple_open ->
        parse_tuple(state)

      :map_open ->
        parse_map(state)

      # Binary literal
      :binary_open ->
        parse_binary_literal(state)

      # Control flow
      :keyword ->
        parse_keyword_prefix(state, token)

      # At sign (decorator / attribute)
      :at ->
        parse_at(state)

      # Indent starts a block
      :indent ->
        parse_block(state)

      _ ->
        error = {:unexpected_token, token.type, token.line, token.col}
        state = add_error(state, error)
        {error_node(token), advance(state)}
    end
  end

  # -- Literals --------------------------------------------------------------

  defp literal(subtype, token) do
    {:literal, [subtype: subtype, line: token.line, col: token.col], token.value}
  end

  defp variable(token) do
    {:variable, [scope: :local, line: token.line, col: token.col], token.value}
  end

  defp error_node(token) do
    {:literal, [subtype: :null, line: token.line, col: token.col, error: true], nil}
  end

  # -- String Interpolation --------------------------------------------------

  defp parse_string_interpolation(state) do
    token = peek(state)
    state = advance(state)
    parts = token.value

    parsed_parts =
      Enum.map(parts, fn
        {:string_part, s} ->
          {:literal, [subtype: :string], s}

        {:expr, expr_tokens} ->
          # Append an EOF token so the sub-parser terminates
          sub_tokens = expr_tokens ++ [Token.new(:eof, nil, token.line, token.col)]
          sub_state = %__MODULE__{tokens: sub_tokens, file: state.file, emit_events: false}
          {expr, _} = parse_expr(sub_state, 0)
          expr
      end)

    ast = {:string_interpolation, [line: token.line, col: token.col], parsed_parts}
    {ast, state}
  end

  # -- Unary Operators -------------------------------------------------------

  defp parse_unary(state, category) do
    token = peek(state)
    state = advance(state)
    rbp = Precedence.prefix_bp(token.type)
    {operand, state} = parse_expr(state, rbp)
    op = Precedence.operator_symbol(token.type)
    ast = {:unary_op, [category: category, operator: op, line: token.line, col: token.col], [operand]}
    {ast, state}
  end

  # -- Grouping ( ... ) ------------------------------------------------------

  defp parse_grouped(state) do
    state = advance(state)
    state = skip_newlines(state)
    {expr, state} = parse_expr(state, 0)
    state = skip_newlines(state)
    state = expect(state, :rparen)
    {expr, state}
  end

  # -- Infix Operators -------------------------------------------------------

  defp handle_infix_op(state, left, token, right_bp, min_bp) do
    case token.type do
      # Pipe desugaring: a |> f  or  a |> f(b, c)
      :pipe ->
        {right, state} = parse_expr(state, right_bp)
        ast = desugar_pipe(left, right, token)
        parse_infix(state, ast, min_bp)

      # Dot access: obj.field -> {:attribute_access, ...}
      :dot ->
        field_token = peek(state)
        state = advance(state)
        field_name = to_string(field_token.value)
        ast = {:attribute_access, [attribute: field_name, line: token.line, col: token.col], [left]}
        parse_infix(state, ast, min_bp)

      # Range operators
      type when type in [:range, :range_inclusive] ->
        {right, state} = parse_expr(state, right_bp)
        inclusive = type == :range_inclusive
        ast = {:range, [inclusive: inclusive, line: token.line, col: token.col], [left, right]}
        parse_infix(state, ast, min_bp)

      # Assignment
      :assign ->
        {right, state} = parse_expr(state, right_bp)
        ast = {:assignment, [line: token.line, col: token.col], [left, right]}
        parse_infix(state, ast, min_bp)

      # Augmented assignment
      type when type in [:plus_assign, :minus_assign, :star_assign, :slash_assign] ->
        {right, state} = parse_expr(state, right_bp)
        op = augmented_op(type)
        ast = {:augmented_assignment, [operator: op, line: token.line, col: token.col], [left, right]}
        parse_infix(state, ast, min_bp)

      # Regular binary operator
      _ ->
        {right, state} = parse_expr(state, right_bp)
        category = Precedence.operator_category(token.type)
        op = Precedence.operator_symbol(token.type)
        ast = {:binary_op, [category: category, operator: op, line: token.line, col: token.col], [left, right]}
        parse_infix(state, ast, min_bp)
    end
  end

  defp augmented_op(:plus_assign), do: :+
  defp augmented_op(:minus_assign), do: :-
  defp augmented_op(:star_assign), do: :*
  defp augmented_op(:slash_assign), do: :/

  # -- Pipe Desugaring -------------------------------------------------------

  defp desugar_pipe(left, right, token) do
    case right do
      {:function_call, meta, args} ->
        name = Keyword.get(meta, :name, "unknown")
        new_meta = Keyword.merge(meta, pipe: true, line: token.line, col: token.col)
        new_meta = Keyword.put(new_meta, :name, name)
        {:function_call, new_meta, [left | args]}

      {:variable, _meta, name} ->
        {:function_call, [name: name, pipe: true, line: token.line, col: token.col], [left]}

      _ ->
        {:function_call, [name: "unknown", pipe: true, line: token.line, col: token.col], [left, right]}
    end
  end

  # -- Function Call ---------------------------------------------------------

  defp parse_call(state, func) do
    token = peek(state)
    state = advance(state)
    {args, state} = parse_call_args(state)
    name = extract_call_name(func)

    meta = [name: name, line: token.line, col: token.col]

    # When the callee is an expression (e.g. f(x)(y)), preserve it so
    # the codegen can compile it as an expression-based call.
    meta =
      if name == "unknown" do
        Keyword.put(meta, :callee, func)
      else
        meta
      end

    ast = {:function_call, meta, args}
    {ast, state}
  end

  defp parse_call_args(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rparen} ->
        {[], advance(state)}

      _ ->
        {first, state} = parse_expr(state, 0)
        state = skip_newlines(state)
        {rest, state} = parse_more_args(state)
        state = skip_newlines(state)
        state = expect(state, :rparen)
        {[first | rest], state}
    end
  end

  defp parse_more_args(state) do
    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        {expr, state} = parse_expr(state, 0)
        state = skip_newlines(state)
        {rest, state} = parse_more_args(state)
        {[expr | rest], state}

      _ ->
        {[], state}
    end
  end

  defp extract_call_name({:variable, _meta, name}), do: name

  defp extract_call_name({:attribute_access, meta, [parent]}) do
    # Reconstruct dotted name: Mod.Sub.func -> "Mod.Sub.func"
    attr = Keyword.get(meta, :attribute, "unknown")
    parent_name = extract_dotted_path(parent)

    case parent_name do
      nil -> attr
      path -> path <> "." <> attr
    end
  end

  defp extract_call_name(_), do: "unknown"

  defp extract_dotted_path({:variable, _, name}), do: name

  defp extract_dotted_path({:attribute_access, meta, [parent]}) do
    attr = Keyword.get(meta, :attribute, "unknown")

    case extract_dotted_path(parent) do
      nil -> attr
      path -> path <> "." <> attr
    end
  end

  defp extract_dotted_path(_), do: nil

  # -- Record Construction / Update  Name{fields}  or  Name{base | overrides} --

  defp parse_record_construction(state, name_ast) do
    open_token = peek(state)
    # consume {
    state = advance(state)

    rec_name =
      case name_ast do
        {:variable, _, n} -> n
        _ -> "unknown"
      end

    line = open_token.line
    col = open_token.col

    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rbrace} ->
        # Empty construction: TypeName{}
        state = advance(state)
        ast = {:function_call, [name: rec_name, record: true, line: line, col: col], []}
        {ast, state}

      _ ->
        # Probe: parse one expression to detect update syntax.
        # :bar ("|") is not an infix operator, so parse_expr stops naturally at it.
        # We save pos+errors so we can fully rewind on a non-update literal.
        saved_pos = state.pos
        saved_errors = state.errors
        {base_expr, probe_state} = parse_expr(state, 0)
        probe_state = skip_newlines(probe_state)

        case peek(probe_state) do
          %Token{type: :bar} ->
            # Record update: TypeName{base | field: val, ...}
            # consume "|"
            probe_state = advance(probe_state)
            probe_state = skip_newlines(probe_state)
            {fields, probe_state} = parse_map_pairs(probe_state, :rbrace)
            probe_state = expect(probe_state, :rbrace)
            ast = {:record_update, [name: rec_name, line: line, col: col], [base_expr | fields]}
            {ast, probe_state}

          _ ->
            # Not update syntax: rewind completely and parse as plain construction.
            state = %{state | pos: saved_pos, errors: saved_errors}
            {fields, state} = parse_map_pairs(state, :rbrace)
            state = expect(state, :rbrace)
            ast = {:function_call, [name: rec_name, record: true, line: line, col: col], fields}
            {ast, state}
        end
    end
  end

  defp is_pascal_case?({:variable, _, <<first, _rest::binary>>}) when first in ?A..?Z, do: true
  defp is_pascal_case?(_), do: false

  # -- Collections -----------------------------------------------------------

  # List: [1, 2, 3] or [h | t] or comprehension [x for x <- list]
  defp parse_list_or_comprehension(state) do
    token = peek(state)
    state = advance(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rbracket} ->
        # Empty list
        {_, state} = {nil, advance(state)}
        {{:list, [line: token.line, col: token.col], []}, state}

      _ ->
        {first, state} = parse_expr(state, 0)
        state = skip_newlines(state)

        case peek(state) do
          # Comprehension: [expr for ...]
          %Token{type: :keyword, value: :for} ->
            parse_comprehension(state, first, token)

          # Cons: [h | t]
          %Token{type: :bar} ->
            state = advance(state)
            state = skip_newlines(state)
            {tail, state} = parse_expr(state, 0)
            state = skip_newlines(state)
            state = expect(state, :rbracket)
            ast = {:list, [cons: true, line: token.line, col: token.col], [first, tail]}
            {ast, state}

          # Regular list
          _ ->
            {rest, state} = parse_comma_exprs(state)
            state = skip_newlines(state)
            state = expect(state, :rbracket)
            ast = {:list, [line: token.line, col: token.col], [first | rest]}
            {ast, state}
        end
    end
  end

  # Tuple: %[a, b, c]
  defp parse_tuple(state) do
    token = peek(state)
    state = advance(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rbracket} ->
        {{:tuple, [line: token.line, col: token.col], []}, advance(state)}

      _ ->
        {first, state} = parse_expr(state, 0)
        {rest, state} = parse_comma_exprs(state)
        state = skip_newlines(state)
        state = expect(state, :rbracket)

        {:tuple, [line: token.line, col: token.col], [first | rest]}
        |> then(&{&1, state})
    end
  end

  # Map: %{k: v, ...} or %{k => v, ...}
  defp parse_map(state) do
    token = peek(state)
    state = advance(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rbrace} ->
        {{:map, [line: token.line, col: token.col], []}, advance(state)}

      _ ->
        {pairs, state} = parse_map_pairs(state, :rbrace)
        state = skip_newlines(state)
        state = expect(state, :rbrace)
        {{:map, [line: token.line, col: token.col], pairs}, state}
    end
  end

  defp parse_map_pairs(state, closing) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: ^closing} ->
        {[], state}

      _ ->
        {pair, state} = parse_map_pair(state)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            {rest, state} = parse_map_pairs(state, closing)
            {[pair | rest], state}

          _ ->
            {[pair], state}
        end
    end
  end

  defp parse_map_pair(state) do
    token = peek(state)
    next = peek_at(state, 1)

    cond do
      # Shorthand: identifier followed by colon  =>  atom key
      token.type == :identifier and next != nil and next.type == :colon ->
        key_atom = String.to_atom(token.value)
        state = advance(state) |> advance()
        state = skip_newlines(state)
        {value, state} = parse_expr(state, 0)
        pair = {:pair, [], [{:literal, [subtype: :symbol], key_atom}, value]}
        {pair, state}

      true ->
        # Explicit: key => value
        {key, state} = parse_expr(state, 0)
        state = skip_newlines(state)
        state = expect(state, :fat_arrow)
        state = skip_newlines(state)
        {value, state} = parse_expr(state, 0)
        pair = {:pair, [], [key, value]}
        {pair, state}
    end
  end

  # Binary literal: <<expr, expr, ...>>
  defp parse_binary_literal(state) do
    token = peek(state)
    state = advance(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :binary_close} ->
        {{:literal, [subtype: :bytes, line: token.line, col: token.col], []}, advance(state)}

      _ ->
        {first, state} = parse_expr(state, 0)
        {rest, state} = parse_comma_exprs(state)
        state = expect(state, :binary_close)
        ast = {:literal, [subtype: :bytes, line: token.line, col: token.col], [first | rest]}
        {ast, state}
    end
  end

  # -- Comprehensions --------------------------------------------------------

  defp parse_comprehension(state, body, open_token) do
    # Already consumed body, currently at `for` keyword
    state = advance(state)
    state = skip_newlines(state)
    {generators_and_filters, state} = parse_generators(state)
    state = skip_newlines(state)
    state = expect(state, :rbracket)
    ast = {:comprehension, [line: open_token.line, col: open_token.col], [body | generators_and_filters]}
    {ast, state}
  end

  defp parse_generators(state) do
    {item, state} = parse_generator_or_filter(state)

    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        {rest, state} = parse_generators(state)
        {[item | rest], state}

      _ ->
        {[item], state}
    end
  end

  defp parse_generator_or_filter(state) do
    # The lexer emits `<` and `-` as separate tokens for `<-`.
    # Strategy: parse LHS at BP above comparison (42) so `<` is not consumed,
    # then check if `< -` follows (generator) or fall back to a full-BP filter.
    saved_pos = state.pos
    {expr, state} = parse_expr(state, 42)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :lt} ->
        next = peek_at(state, 1)

        if next != nil and next.type == :minus do
          # Generator: pattern <- collection
          state = advance(state) |> advance()
          state = skip_newlines(state)
          {collection, state} = parse_expr(state, 0)
          {{:generator, [], [expr, collection]}, state}
        else
          # Not a generator. Re-parse from saved position at BP 0 for full filter expression.
          state = %{state | pos: saved_pos}
          {filter_expr, state} = parse_expr(state, 0)
          {{:filter, [], [filter_expr]}, state}
        end

      _ ->
        # Check if the high-BP parse left something behind (e.g. `x > 0`).
        # If the expression was just a variable and there's an operator next, re-parse at BP 0.
        token = peek(state)

        if Precedence.infix_bp(token.type) != :not_infix do
          state = %{state | pos: saved_pos}
          {filter_expr, state} = parse_expr(state, 0)
          {{:filter, [], [filter_expr]}, state}
        else
          {{:filter, [], [expr]}, state}
        end
    end
  end

  # -- Keyword-Triggered Prefix Expressions ----------------------------------

  defp parse_keyword_prefix(state, token) do
    case token.value do
      :let ->
        parse_let(state)

      :if ->
        parse_if(state)

      :match ->
        parse_match(state)

      :return ->
        parse_keyword_unary(state, :early_return)

      :throw ->
        parse_keyword_unary(state, :throw)

      :yield ->
        parse_keyword_unary(state, :yield)

      :spawn ->
        parse_keyword_unary(state, :async_operation)

      :send ->
        parse_send(state)

      :receive ->
        parse_receive(state)

      :try ->
        parse_try(state)

      # Structural constructs (Milestone 3)
      :fn ->
        parse_fn_or_lambda(state)

      :local ->
        parse_local(state)

      :mod ->
        parse_module(state)

      :rec ->
        parse_record(state)

      :type ->
        parse_type_def(state)

      :proto ->
        parse_proto(state)

      :impl ->
        parse_impl(state)

      :fsm ->
        parse_fsm(state)

      :use ->
        parse_use(state)

      _ ->
        # Treat unknown keywords as identifiers (e.g., type names used as values)
        {variable(token), advance(state)}
    end
  end

  # -- Let Binding -----------------------------------------------------------

  defp parse_let(state) do
    token = peek(state)
    state = advance(state)

    # Parse pattern (LHS) at high enough BP to NOT consume `=`
    # Assignment has BP 5, so parsing at BP 6 stops before `=`
    {pattern, state} = parse_expr(state, 6)

    # Check for type annotation
    {type_ann, state} =
      case peek(state) do
        %Token{type: :colon} ->
          state = advance(state)
          {type_expr, state} = parse_type_expr(state)
          {type_expr, state}

        _ ->
          {nil, state}
      end

    # Expect =
    state = expect(state, :assign)
    state = skip_newlines(state)

    # Parse value (RHS) -- might be an indented block
    {value, state} = parse_expr_or_block(state)

    meta = [let: true, line: token.line, col: token.col]
    meta = if type_ann, do: Keyword.put(meta, :type_annotation, type_ann), else: meta

    ast = {:assignment, meta, [pattern, value]}
    {ast, state}
  end

  # -- If / Elif / Else

  defp parse_if(state) do
    token = peek(state)
    state = advance(state)

    # Parse condition
    {condition, state} = parse_expr(state, 0)
    state = skip_newlines(state)

    # Inline form: if cond then a else b
    # Block form: if cond <newline> <indent> ... <dedent> [elif ...] [else ...]
    case peek(state) do
      %Token{type: :keyword, value: :then} ->
        state = advance(state)
        {then_branch, state} = parse_expr(state, 0)

        {else_branch, state} =
          case peek(state) do
            %Token{type: :keyword, value: :else} ->
              state = advance(state)
              parse_expr(state, 0)

            _ ->
              {{:literal, [subtype: :null], nil}, state}
          end

        ast = {:conditional, [line: token.line, col: token.col], [condition, then_branch, else_branch]}
        {ast, state}

      _ ->
        # Block form
        {then_branch, state} = parse_block(state)

        state = skip_newlines(state)

        {else_branch, state} =
          case peek(state) do
            %Token{type: :keyword, value: :elif} ->
              # Desugar elif to nested conditional
              parse_if(state)

            %Token{type: :keyword, value: :else} ->
              state = advance(state)
              state = skip_newlines(state)
              parse_block(state)

            _ ->
              {{:literal, [subtype: :null], nil}, state}
          end

        ast = {:conditional, [line: token.line, col: token.col], [condition, then_branch, else_branch]}
        {ast, state}
    end
  end

  # -- Match Expression ------------------------------------------------------

  defp parse_match(state) do
    token = peek(state)
    state = advance(state)

    # Parse scrutinee
    {scrutinee, state} = parse_expr(state, 0)
    state = skip_newlines(state)

    # Inline form: match x { pat -> body, ... }
    # Block form: match x <newline> <indent> arms <dedent>
    case peek(state) do
      %Token{type: :lbrace} ->
        state = advance(state)
        {arms, state} = parse_inline_match_arms(state)
        state = expect(state, :rbrace)
        ast = {:pattern_match, [line: token.line, col: token.col], [scrutinee | arms]}
        {ast, state}

      %Token{type: :indent} ->
        state = advance(state)
        {arms, state} = parse_block_match_arms(state)
        state = expect_dedent(state)
        ast = {:pattern_match, [line: token.line, col: token.col], [scrutinee | arms]}
        {ast, state}

      _ ->
        ast = {:pattern_match, [line: token.line, col: token.col], [scrutinee]}
        {ast, state}
    end
  end

  defp parse_inline_match_arms(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rbrace} ->
        {[], state}

      _ ->
        {arm, state} = parse_match_arm(state)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            state = skip_newlines(state)
            {rest, state} = parse_inline_match_arms(state)
            {[arm | rest], state}

          _ ->
            {[arm], state}
        end
    end
  end

  defp parse_block_match_arms(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {[], state}

      _ ->
        {arm, state} = parse_match_arm(state)
        state = skip_newlines(state)
        {rest, state} = parse_block_match_arms(state)
        {[arm | rest], state}
    end
  end

  defp parse_match_arm(state) do
    # Parse pattern
    {pattern, state} = parse_expr(state, 0)
    state = skip_newlines(state)

    # Optional guard: when expr
    {guard, state} =
      case peek(state) do
        %Token{type: :keyword, value: :when} ->
          state = advance(state)
          {g, state} = parse_expr(state, 0)
          {g, state}

        _ ->
          {nil, state}
      end

    # Expect ->
    state = expect(state, :arrow)
    state = skip_newlines(state)

    # Parse body
    {body, state} = parse_expr_or_block(state)

    meta = if guard, do: [pattern: pattern, guard: guard], else: [pattern: pattern]

    {:match_arm, meta, [body]}
    |> then(&{&1, state})
  end

  # -- fn: named function or lambda ------------------------------------------

  defp parse_fn_or_lambda(state) do
    token = peek(state)
    state = advance(state)

    # fn followed by ( -> lambda
    # fn followed by identifier or (soft) keyword -> named function definition
    #
    # Some Cure keywords (spawn, send, receive, after) are ordinary
    # function names in other languages, and `Std.Fsm` defines e.g.
    # `fn spawn(fsm_module: Atom) -> Pid`. Let those keywords double as
    # function-definition names; they still behave as keywords in
    # statement position.
    case peek(state) do
      %Token{type: :lparen} ->
        parse_lambda_body(state, token)

      %Token{type: :identifier} ->
        parse_fn_def(state, token, :public)

      %Token{type: :keyword} ->
        parse_fn_def(state, token, :public)

      _ ->
        parse_lambda_body(state, token)
    end
  end

  # local fn name(...) -> private function
  defp parse_local(state) do
    token = peek(state)
    state = advance(state)

    # Expect fn keyword next
    case peek(state) do
      %Token{type: :keyword, value: :fn} ->
        state = advance(state)
        # After `local fn`, a name (identifier or soft keyword) must follow.
        case peek(state) do
          %Token{type: type} when type in [:identifier, :keyword] ->
            parse_fn_def(state, token, :private)

          _ ->
            parse_lambda_body(state, token)
        end

      _ ->
        error = {:expected, :fn, :got, peek(state).type, token.line, token.col}
        state = add_error(state, error)
        {error_node(token), state}
    end
  end

  # -- Named Function Definition ---------------------------------------------

  defp parse_fn_def(state, fn_token, visibility) do
    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    # Parse parameter list
    state = expect(state, :lparen)
    {params, state} = parse_typed_params(state)
    state = expect(state, :rparen)

    # Optional return type: -> Type
    {return_type, state} =
      case peek(state) do
        %Token{type: :arrow} ->
          state = advance(state)
          parse_type_expr(state)

        _ ->
          {nil, state}
      end

    # Optional effect annotation: ! Effect, Effect2
    {effects, state} =
      case peek(state) do
        %Token{type: :bang} ->
          state = advance(state)
          parse_effect_list(state)

        _ ->
          {nil, state}
      end

    # Optional guard: when expr
    # Parse at BP 6 to stop before `=` (BP 5) so the guard doesn't consume the body
    {guard, state} =
      case peek(state) do
        %Token{type: :keyword, value: :when} ->
          state = advance(state)
          {g, state} = parse_expr(state, 6)
          {g, state}

        _ ->
          {nil, state}
      end

    # Optional constraints: where Proto(T), ...
    {constraints, state} =
      case peek(state) do
        %Token{type: :keyword, value: :where} ->
          state = advance(state)
          parse_constraint_list(state)

        _ ->
          {[], state}
      end

    state = skip_newlines(state)

    # Check for multi-clause form (indented | patterns) or = body
    case peek(state) do
      %Token{type: :assign} ->
        state = advance(state)
        state = skip_newlines(state)
        {body, state} = parse_expr_or_block(state)

        meta = build_fn_meta(fn_token, name, params, return_type, visibility, guard, constraints, effects)
        ast = {:function_def, meta, [body]}
        {ast, state}

      %Token{type: :indent} ->
        # Could be multi-clause: indented | pattern -> body lines
        state = advance(state)
        {clauses, state} = parse_fn_clauses(state)
        state = expect_dedent(state)

        meta = build_fn_meta(fn_token, name, params, return_type, visibility, guard, constraints, effects)
        meta = Keyword.put(meta, :clauses, clauses)
        ast = {:function_def, meta, []}
        {ast, state}

      _ ->
        # Function signature only (no body, e.g. in protocol)
        meta = build_fn_meta(fn_token, name, params, return_type, visibility, guard, constraints, effects)
        ast = {:function_def, meta, []}
        {ast, state}
    end
  end

  defp build_fn_meta(fn_token, name, params, return_type, visibility, guard, constraints, effects) do
    meta = [
      name: name,
      params: params,
      visibility: visibility,
      arity: length(params),
      line: fn_token.line,
      col: fn_token.col
    ]

    meta = if return_type, do: Keyword.put(meta, :return_type, return_type), else: meta
    meta = if guard, do: Keyword.put(meta, :guards, guard), else: meta
    meta = if constraints != [], do: Keyword.put(meta, :constraints, constraints), else: meta
    meta = if effects, do: Keyword.put(meta, :effects, effects), else: meta
    meta
  end

  defp parse_fn_clauses(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {[], state}

      %Token{type: :bar} ->
        state = advance(state)
        {clause, state} = parse_single_fn_clause(state)
        state = skip_newlines(state)
        {rest, state} = parse_fn_clauses(state)
        {[clause | rest], state}

      _ ->
        {[], state}
    end
  end

  defp parse_single_fn_clause(state) do
    # Parse pattern(s) until -> or when
    {patterns, state} = parse_clause_patterns(state, [])

    # Optional guard
    {guard, state} =
      case peek(state) do
        %Token{type: :keyword, value: :when} ->
          state = advance(state)
          {g, state} = parse_expr(state, 0)
          {g, state}

        _ ->
          {nil, state}
      end

    state = expect(state, :arrow)
    state = skip_newlines(state)
    {body, state} = parse_expr_or_block(state)

    clause = %{params: patterns, guard: guard, body: [body]}
    {clause, state}
  end

  defp parse_clause_patterns(state, acc) do
    case peek(state) do
      %Token{type: :arrow} ->
        {Enum.reverse(acc), state}

      %Token{type: :keyword, value: :when} ->
        {Enum.reverse(acc), state}

      _ ->
        {pat, state} = parse_expr(state, 42)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            state = skip_newlines(state)
            parse_clause_patterns(state, [pat | acc])

          _ ->
            {Enum.reverse([pat | acc]), state}
        end
    end
  end

  # -- Typed Parameters  name: Type [= default] ------------------------------

  defp parse_typed_params(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rparen} -> {[], state}
      _ -> parse_typed_params_list(state)
    end
  end

  defp parse_typed_params_list(state) do
    {param, state} = parse_single_typed_param(state)
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        {rest, state} = parse_typed_params_list(state)
        {[param | rest], state}

      _ ->
        {[param], state}
    end
  end

  defp parse_single_typed_param(state) do
    # Check for variadic: *name or **name
    {kind, state} =
      case peek(state) do
        %Token{type: :star} ->
          next = peek_at(state, 1)

          if next && next.type == :star do
            {_, state} = {nil, advance(state) |> advance()}
            {:keyword_variadic, state}
          else
            {_, state} = {nil, advance(state)}
            {:variadic, state}
          end

        _ ->
          {:positional, state}
      end

    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    # Optional type annotation: : Type
    {type_ast, state} =
      case peek(state) do
        %Token{type: :colon} ->
          state = advance(state)
          parse_type_expr(state)

        _ ->
          {nil, state}
      end

    # Optional default value: = expr
    {default, state} =
      case peek(state) do
        %Token{type: :assign} ->
          state = advance(state)
          state = skip_newlines(state)
          {d, state} = parse_expr(state, 6)
          {d, state}

        _ ->
          {nil, state}
      end

    param_meta = []
    param_meta = if type_ast, do: Keyword.put(param_meta, :type, type_ast), else: param_meta
    param_meta = if default, do: Keyword.put(param_meta, :default, default), else: param_meta
    param_meta = if kind != :positional, do: Keyword.put(param_meta, :kind, kind), else: param_meta

    {{:param, param_meta, name}, state}
  end

  # -- Lambda (anonymous fn) -------------------------------------------------

  defp parse_lambda_body(state, token) do
    state = expect(state, :lparen)
    {params, state} = parse_lambda_params(state)
    state = expect(state, :rparen)
    state = expect(state, :arrow)
    state = skip_newlines(state)
    {body, state} = parse_expr_or_block(state)

    param_nodes = Enum.map(params, fn name -> {:param, [], name} end)
    ast = {:lambda, [params: param_nodes, line: token.line, col: token.col], [body]}
    {ast, state}
  end

  defp parse_lambda_params(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rparen} ->
        {[], state}

      _ ->
        name = peek(state).value
        state = advance(state)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            state = skip_newlines(state)
            {rest, state} = parse_lambda_params(state)
            {[to_string(name) | rest], state}

          _ ->
            {[to_string(name)], state}
        end
    end
  end

  # -- Module  mod Name.Path -------------------------------------------------

  defp parse_module(state) do
    token = peek(state)
    state = advance(state)

    # Parse module name (dotted path)
    {name, state} = parse_dotted_name(state)
    state = skip_newlines(state)

    # Parse indented body
    {body_stmts, state} = parse_definition_block(state)

    meta = [container_type: :module, name: name, language: :cure, line: token.line, col: token.col]
    ast = {:container, meta, body_stmts}
    {ast, state}
  end

  # -- Record  rec Name [(TypeParams)] ---------------------------------------

  defp parse_record(state) do
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    # Optional type params: (A, B)
    {type_params, state} =
      case peek(state) do
        %Token{type: :lparen} ->
          state = advance(state)
          {tp, state} = parse_name_list(state, :rparen)
          state = expect(state, :rparen)
          {tp, state}

        _ ->
          {[], state}
      end

    state = skip_newlines(state)

    # Parse indented fields: name: Type
    {fields, state} = parse_record_fields(state)

    meta = [container_type: :struct, name: name, line: token.line, col: token.col]
    meta = if type_params != [], do: Keyword.put(meta, :type_params, type_params), else: meta
    ast = {:container, meta, fields}
    {ast, state}
  end

  defp parse_record_fields(state) do
    case peek(state) do
      %Token{type: :indent} ->
        state = advance(state)
        {fields, state} = parse_record_field_list(state)
        state = expect_dedent(state)
        {fields, state}

      _ ->
        {[], state}
    end
  end

  defp parse_record_field_list(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {[], state}

      _ ->
        name_token = peek(state)
        state = advance(state)
        state = expect(state, :colon)
        {type_ast, state} = parse_type_expr(state)
        state = skip_newlines(state)

        field = {:param, [type: type_ast], to_string(name_token.value)}
        {rest, state} = parse_record_field_list(state)
        {[field | rest], state}
    end
  end

  # -- Type  type Name[(Params)] = ... ---------------------------------------

  defp parse_type_def(state) do
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    # Optional type params
    {type_params, state} =
      case peek(state) do
        %Token{type: :lparen} ->
          state = advance(state)
          {tp, state} = parse_name_list(state, :rparen)
          state = expect(state, :rparen)
          {tp, state}

        _ ->
          {[], state}
      end

    state = expect(state, :assign)
    state = skip_newlines(state)

    # Check if RHS is a refinement type: {x: T | pred}
    case peek(state) do
      %Token{type: :lbrace} ->
        {refinement, state} = parse_refinement_type(state)
        meta = [name: name, refinement: true, line: token.line, col: token.col]
        meta = if type_params != [], do: Keyword.put(meta, :type_params, type_params), else: meta
        ast = {:type_annotation, meta, refinement}
        {ast, state}

      _ ->
        # Parse as ADT variants (A(T) | B | C) or type alias
        {first_variant, state} = parse_type_variant(state)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: :bar} ->
            # ADT: multiple variants separated by |
            {rest_variants, state} = parse_more_variants(state)
            variants = [first_variant | rest_variants]
            meta = [container_type: :enum, name: name, line: token.line, col: token.col]
            meta = if type_params != [], do: Keyword.put(meta, :type_params, type_params), else: meta
            ast = {:container, meta, variants}
            {ast, state}

          _ ->
            # Type alias: type Name = ExistingType
            meta = [name: name, line: token.line, col: token.col]
            meta = if type_params != [], do: Keyword.put(meta, :type_params, type_params), else: meta
            ast = {:type_annotation, meta, [first_variant]}
            {ast, state}
        end
    end
  end

  defp parse_type_variant(state) do
    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    case peek(state) do
      %Token{type: :lparen} ->
        # Constructor with params: Some(T)
        state = advance(state)
        {params, state} = parse_type_param_list(state)
        state = expect(state, :rparen)
        ast = {:function_def, [name: name, params: params, variant: true], []}
        {ast, state}

      _ ->
        # Nullary constructor: None
        {{:variable, [variant: true], name}, state}
    end
  end

  defp parse_more_variants(state) do
    case peek(state) do
      %Token{type: :bar} ->
        state = advance(state)
        state = skip_newlines(state)
        {variant, state} = parse_type_variant(state)
        state = skip_newlines(state)
        {rest, state} = parse_more_variants(state)
        {[variant | rest], state}

      _ ->
        {[], state}
    end
  end

  defp parse_type_param_list(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rparen} ->
        {[], state}

      _ ->
        {t, state} = parse_type_expr(state)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            state = skip_newlines(state)
            {rest, state} = parse_type_param_list(state)
            {[t | rest], state}

          _ ->
            {[t], state}
        end
    end
  end

  defp parse_refinement_type(state) do
    # {x: BaseType | predicate}
    state = advance(state)
    var_token = peek(state)
    state = advance(state)
    state = expect(state, :colon)
    {base_type, state} = parse_type_expr(state)
    state = expect(state, :bar)
    state = skip_newlines(state)
    {predicate, state} = parse_expr(state, 0)
    state = expect(state, :rbrace)

    var_ast = {:variable, [scope: :local], to_string(var_token.value)}
    {[var_ast, base_type, predicate], state}
  end

  # -- Protocol  proto Name(T) -----------------------------------------------

  defp parse_proto(state) do
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    # Type params: (T) or (T, U)
    {type_params, state} =
      case peek(state) do
        %Token{type: :lparen} ->
          state = advance(state)
          {tp, state} = parse_name_list(state, :rparen)
          state = expect(state, :rparen)
          {tp, state}

        _ ->
          {[], state}
      end

    state = skip_newlines(state)
    {body, state} = parse_definition_block(state)

    meta = [
      container_type: :protocol,
      name: name,
      type_params: type_params,
      line: token.line,
      col: token.col
    ]

    ast = {:container, meta, body}
    {ast, state}
  end

  # -- Implementation  impl Proto for Type -----------------------------------

  defp parse_impl(state) do
    token = peek(state)
    state = advance(state)

    # Protocol name
    {proto_name, state} = parse_dotted_name(state)

    # Expect `for`
    state = expect(state, :keyword)
    # ^ consumes the `for` keyword token

    # Type being implemented
    {for_type, state} = parse_type_expr(state)

    # Optional where clause
    {constraints, state} =
      case peek(state) do
        %Token{type: :keyword, value: :where} ->
          state = advance(state)
          parse_constraint_list(state)

        _ ->
          {[], state}
      end

    state = skip_newlines(state)
    {body, state} = parse_definition_block(state)

    for_name =
      case for_type do
        {:variable, _, n} -> n
        {:function_call, m, _} -> Keyword.get(m, :name, "unknown")
        _ -> "unknown"
      end

    meta = [
      container_type: :trait,
      name: "#{proto_name}.#{for_name}",
      protocol: proto_name,
      for: for_name,
      line: token.line,
      col: token.col
    ]

    meta = if constraints != [], do: Keyword.put(meta, :constraints, constraints), else: meta
    ast = {:container, meta, body}
    {ast, state}
  end

  # -- Import  use Path.{items} [as Alias] -----------------------------------

  defp parse_use(state) do
    token = peek(state)
    state = advance(state)

    # Parse module path
    {path, state} = parse_dotted_name(state)

    # Check for selective import: .{a, b, c}
    {items, state} =
      case peek(state) do
        %Token{type: :dot} ->
          next = peek_at(state, 1)

          if next && next.type == :lbrace do
            state = advance(state) |> advance()
            {names, state} = parse_name_list(state, :rbrace)
            state = expect(state, :rbrace)
            {names, state}
          else
            {[], state}
          end

        _ ->
          {[], state}
      end

    # Check for alias: as Name
    {alias_name, state} =
      case peek(state) do
        %Token{type: :keyword, value: :as} ->
          state = advance(state)
          a = peek(state)
          state = advance(state)
          {to_string(a.value), state}

        _ ->
          {nil, state}
      end

    meta = [source: path, import_type: :use, language: :cure, line: token.line, col: token.col]
    meta = if items != [], do: Keyword.put(meta, :items, items), else: meta
    meta = if alias_name, do: Keyword.put(meta, :alias, alias_name), else: meta
    ast = {:import, meta, []}
    {ast, state}
  end

  # -- FSM  fsm Name with Payload{...} --------------------------------------

  defp parse_fsm(state) do
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    # Expect `with`
    {payload, state} =
      case peek(state) do
        %Token{type: :keyword, value: :in} ->
          # `with` is not a keyword; reuse `in` or handle identifier
          state = advance(state)
          {p, state} = parse_expr(state, 0)
          {p, state}

        %Token{type: :identifier, value: "with"} ->
          state = advance(state)
          {p, state} = parse_expr(state, 0)
          {p, state}

        _ ->
          {nil, state}
      end

    state = skip_newlines(state)

    # Parse indented body: transitions, @terminal, @invariant, @verify
    {fsm_body, meta_additions, state} = parse_fsm_block(state)

    meta =
      [container_type: :fsm, name: name, line: token.line, col: token.col] ++ meta_additions

    meta = if payload, do: Keyword.put(meta, :payload, payload), else: meta
    ast = {:container, meta, fsm_body}
    {ast, state}
  end

  defp parse_fsm_block(state) do
    case peek(state) do
      %Token{type: :indent} ->
        state = advance(state)
        {items, meta_acc, state} = parse_fsm_items(state, [], [])
        state = expect_dedent(state)
        {items, meta_acc, state}

      _ ->
        {[], [], state}
    end
  end

  @fsm_callback_names ~w(on_transition on_enter on_exit on_failure on_timer)

  defp parse_fsm_items(state, items_acc, meta_acc) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {Enum.reverse(items_acc), meta_acc, state}

      %Token{type: :at} ->
        # @terminal, @invariant, @verify, @timer
        {new_meta, state} = parse_fsm_annotation(state)
        state = skip_newlines(state)
        parse_fsm_items(state, items_acc, meta_acc ++ new_meta)

      %Token{type: :identifier, value: cb_name} when cb_name in @fsm_callback_names ->
        # Callback block: on_transition, on_enter, on_exit, on_failure, on_timer
        {new_meta, state} = parse_fsm_callback(state)
        state = skip_newlines(state)
        parse_fsm_items(state, items_acc, meta_acc ++ new_meta)

      _ ->
        # Transition line: Source --event--> Target
        {transition, state} = parse_fsm_transition(state)
        state = skip_newlines(state)
        parse_fsm_items(state, [transition | items_acc], meta_acc)
    end
  end

  defp parse_fsm_annotation(state) do
    state = advance(state)
    name_token = peek(state)
    name = to_string(name_token.value)
    state = advance(state)

    case name do
      "terminal" ->
        val_token = peek(state)
        state = advance(state)
        {[terminal_states: [to_string(val_token.value)]], state}

      "invariant" ->
        {expr, state} = parse_expr(state, 0)
        {[invariants: [expr]], state}

      "verify" ->
        {expr, state} = parse_expr(state, 0)
        {[verify: [expr]], state}

      "timer" ->
        val_token = peek(state)
        state = advance(state)

        ms =
          case val_token do
            %Token{type: :integer, value: v} -> v
            _ -> String.to_integer(to_string(val_token.value))
          end

        {[timer: ms], state}

      _ ->
        {[], state}
    end
  end

  # -- FSM callback blocks: on_transition, on_enter, on_exit, on_failure, on_timer
  #
  # Clauses are written as:
  #   (pattern1, pattern2, ...) -> body
  # or with a guard:
  #   (pattern1, pattern2, ...) when guard -> body
  #
  # The parenthesized patterns are parsed as comma-separated expressions and
  # assembled into a {:tuple, [], [patterns...]} node to match the callback arity.

  defp parse_fsm_callback(state) do
    name_token = peek(state)
    cb_name = String.to_atom(name_token.value)
    state = advance(state)
    state = skip_newlines(state)

    {clauses, state} =
      case peek(state) do
        %Token{type: :indent} ->
          state = advance(state)
          {arms, state} = parse_fsm_callback_clauses(state)
          state = expect_dedent(state)
          {arms, state}

        _ ->
          {arm, state} = parse_fsm_callback_clause(state)
          {[arm], state}
      end

    {[{cb_name, clauses}], state}
  end

  defp parse_fsm_callback_clauses(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {[], state}

      _ ->
        {arm, state} = parse_fsm_callback_clause(state)
        state = skip_newlines(state)
        {rest, state} = parse_fsm_callback_clauses(state)
        {[arm | rest], state}
    end
  end

  # Parse a single FSM callback clause: (pat1, pat2, ...) [when guard] -> body
  defp parse_fsm_callback_clause(state) do
    # Expect opening paren
    state = expect(state, :lparen)

    # Parse comma-separated pattern expressions
    {patterns, state} = parse_fsm_callback_params(state)

    # Expect closing paren
    state = expect(state, :rparen)
    state = skip_newlines(state)

    # Optional guard: when expr
    {guard, state} =
      case peek(state) do
        %Token{type: :keyword, value: :when} ->
          state = advance(state)
          {g, state} = parse_expr(state, 0)
          {g, state}

        _ ->
          {nil, state}
      end

    # Expect ->
    state = expect(state, :arrow)
    state = skip_newlines(state)

    # Parse body
    {body, state} = parse_expr_or_block(state)

    # Assemble patterns into a tuple node
    pattern = {:tuple, [], patterns}
    meta = if guard, do: [pattern: pattern, guard: guard], else: [pattern: pattern]

    {{:match_arm, meta, [body]}, state}
  end

  defp parse_fsm_callback_params(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :rparen} ->
        {[], state}

      _ ->
        {expr, state} = parse_expr(state, 0)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            state = skip_newlines(state)
            {rest, state} = parse_fsm_callback_params(state)
            {[expr | rest], state}

          _ ->
            {[expr], state}
        end
    end
  end

  defp parse_fsm_transition(state) do
    # Source --event[!?] [when guard] [do actions]--> Target
    # or * --event--> Target (wildcard)
    from_token = peek(state)

    from =
      case from_token.type do
        :star -> "*"
        _ -> to_string(from_token.value)
      end

    state = advance(state)

    # Expect transition_open (--)
    state = expect(state, :transition_open)

    # Event name and optional guard/action are lexed as tokens between -- and -->
    {event, guard, action, state} = parse_transition_body(state)

    # Detect event kind from suffix: ! = hard, ? = soft, otherwise normal
    {event_base, event_kind} = classify_event(event)

    # After transition_close (-->), parse target
    target_token = peek(state)
    target = to_string(target_token.value)
    state = advance(state)

    meta = [name: "transition", from: from, event: event_base, to: target, event_kind: event_kind]
    meta = if guard, do: Keyword.put(meta, :guard, guard), else: meta
    meta = if action, do: Keyword.put(meta, :action, action), else: meta

    ast = {:function_call, meta, []}
    {ast, state}
  end

  defp classify_event(event) when is_binary(event) do
    cond do
      String.ends_with?(event, "!") -> {String.trim_trailing(event, "!"), :hard}
      String.ends_with?(event, "?") -> {String.trim_trailing(event, "?"), :soft}
      true -> {event, :normal}
    end
  end

  defp classify_event(event), do: {to_string(event), :normal}

  defp parse_transition_body(state) do
    # Read tokens until :transition_close
    {event_name, state} = read_transition_event(state)

    # Check for guard: when ...
    {guard, state} =
      case peek(state) do
        %Token{type: :keyword, value: :when} ->
          state = advance(state)
          {g, state} = parse_until_transition_close_or_do(state)
          {g, state}

        _ ->
          {nil, state}
      end

    # Check for action: do ...
    {action, state} =
      case peek(state) do
        %Token{type: :keyword, value: :do} ->
          state = advance(state)
          {a, state} = parse_until_transition_close(state)
          {a, state}

        _ ->
          {nil, state}
      end

    # Consume transition_close
    state = expect(state, :transition_close)
    state = skip_newlines(state)

    {event_name, guard, action, state}
  end

  defp read_transition_event(state) do
    token = peek(state)

    case token.type do
      :transition_close -> {"", state}
      :keyword -> {to_string(token.value), advance(state)}
      :identifier -> {token.value, advance(state)}
      _ -> {to_string(token.value), advance(state)}
    end
  end

  defp parse_until_transition_close_or_do(state) do
    # Parse an expression, stopping before --> or `do`
    {expr, state} = parse_expr(state, 0)
    {expr, state}
  end

  defp parse_until_transition_close(state) do
    {expr, state} = parse_expr(state, 0)
    {expr, state}
  end

  # -- Enhanced Type Expression Parser ----------------------------------------

  # Replaces the simple version from Milestone 2.
  # Handles: PascalCase, Type(A, B), A -> B, (A, B) -> C, {x: T | pred}
  defp parse_type_expr(state) do
    token = peek(state)

    case token.type do
      :lparen ->
        # Tuple type or function type: (A, B) -> C
        state = advance(state)
        {inner, state} = parse_type_param_list(state)
        state = expect(state, :rparen)

        case peek(state) do
          %Token{type: :arrow} ->
            state = advance(state)
            {ret, state} = parse_type_expr(state)
            ast = {:function_call, [name: "Function", function_type: true], inner ++ [ret]}
            {ast, state}

          _ ->
            # Just a grouped type or tuple type
            case inner do
              [single] -> {single, state}
              _ -> {{:tuple, [], inner}, state}
            end
        end

      :lbrace ->
        # Refinement type: {x: T | pred}
        {parts, state} = parse_refinement_type(state)
        {{:type_annotation, [refinement: true], parts}, state}

      _ ->
        # Simple type: Name or Name(A, B)
        state = advance(state)
        base_name = to_string(token.value)

        case peek(state) do
          %Token{type: :lparen} ->
            state = advance(state)
            {params, state} = parse_type_param_list(state)
            state = expect(state, :rparen)
            ast = {:function_call, [name: base_name], params}
            maybe_parse_function_type(state, ast)

          %Token{type: :arrow} ->
            # A -> B  (unary function type)
            state = advance(state)
            {ret, state} = parse_type_expr(state)
            base = {:variable, [scope: :local], base_name}
            ast = {:function_call, [name: "Function", function_type: true], [base, ret]}
            {ast, state}

          _ ->
            base = {:variable, [scope: :local], base_name}
            {base, state}
        end
    end
  end

  defp maybe_parse_function_type(state, left) do
    case peek(state) do
      %Token{type: :arrow} ->
        state = advance(state)
        {ret, state} = parse_type_expr(state)

        params =
          case left do
            {:function_call, _, p} -> p
            _ -> [left]
          end

        ast = {:function_call, [name: "Function", function_type: true], params ++ [ret]}
        {ast, state}

      _ ->
        {left, state}
    end
  end

  # -- Effect List  ! Io, Exception ------------------------------------------

  defp parse_effect_list(state) do
    state = skip_newlines(state)
    {first, state} = parse_single_effect(state)

    {rest, state} =
      case peek(state) do
        %Token{type: :comma} ->
          state = advance(state)
          state = skip_newlines(state)
          {more, state} = parse_effect_list_tail(state)
          {more, state}

        _ ->
          {[], state}
      end

    {[first | rest], state}
  end

  defp parse_effect_list_tail(state) do
    {eff, state} = parse_single_effect(state)

    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        {rest, state} = parse_effect_list_tail(state)
        {[eff | rest], state}

      _ ->
        {[eff], state}
    end
  end

  defp parse_single_effect(state) do
    token = peek(state)
    state = advance(state)
    name = to_string(token.value)

    effect =
      case String.downcase(name) do
        "io" -> :io
        "state" -> :state
        "exception" -> :exception
        "spawn" -> :spawn
        "extern" -> :extern
        _ -> String.to_atom(String.downcase(name))
      end

    {effect, state}
  end

  # -- Constraint List  Proto(T), Proto2(U) ----------------------------------

  defp parse_constraint_list(state) do
    {first, state} = parse_single_constraint(state)

    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        {rest, state} = parse_constraint_list(state)
        {[first | rest], state}

      _ ->
        {[first], state}
    end
  end

  defp parse_single_constraint(state) do
    # Proto(T) form
    name_token = peek(state)
    state = advance(state)
    name = to_string(name_token.value)

    case peek(state) do
      %Token{type: :lparen} ->
        state = advance(state)
        {params, state} = parse_type_param_list(state)
        state = expect(state, :rparen)
        {{:function_call, [name: name, constraint: true], params}, state}

      _ ->
        {{:variable, [constraint: true], name}, state}
    end
  end

  # -- Helpers: dotted names, name lists, definition blocks ------------------

  defp parse_dotted_name(state) do
    first = peek(state)
    state = advance(state)
    parse_dotted_name(state, to_string(first.value))
  end

  defp parse_dotted_name(state, acc) do
    case peek(state) do
      %Token{type: :dot} ->
        # Don't consume dot if next token is { (selective import syntax)
        next = peek_at(state, 1)

        if next && next.type in [:lbrace, :lbracket] do
          {acc, state}
        else
          state = advance(state)
          next_token = peek(state)
          state = advance(state)
          parse_dotted_name(state, acc <> "." <> to_string(next_token.value))
        end

      _ ->
        {acc, state}
    end
  end

  defp parse_name_list(state, closing) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: ^closing} ->
        {[], state}

      _ ->
        token = peek(state)
        state = advance(state)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: :comma} ->
            state = advance(state)
            {rest, state} = parse_name_list(state, closing)
            {[to_string(token.value) | rest], state}

          _ ->
            {[to_string(token.value)], state}
        end
    end
  end

  # Parse an indented block of definitions (for mod, proto, impl bodies)
  #
  # Tolerates doc_comment tokens that precede the leading `:indent` --
  # the lexer emits fenced `###...###` docstrings *before* measuring the
  # indentation of the line that follows, so a module body like
  #
  #     mod M
  #       ###
  #       description
  #       ###
  #       fn f() -> Int = 0
  #
  # will have the token stream `[mod, M, newline, doc_comment, indent,
  # fn, ...]`. Prior to v0.17.0 we would bail out with an empty body.
  # Now we carry the doc forward to attach to the first definition
  # inside the block (if any).
  defp parse_definition_block(state) do
    {leading_doc, state} = collect_leading_docs(state)

    case peek(state) do
      %Token{type: :indent} ->
        state = advance(state)
        {stmts, state} = parse_block_body(state)
        state = expect_dedent(state)
        {attach_leading_doc(stmts, leading_doc), state}

      _ ->
        {[], state}
    end
  end

  # Collect any doc_comment tokens (intermixed with newlines) and return
  # their concatenated text plus the advanced state. Returns `{"", state}`
  # when there are no doc comments to consume.
  defp collect_leading_docs(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :doc_comment} ->
        {text, state} = collect_doc_comments(state)
        state = skip_newlines(state)
        {text, state}

      _ ->
        {"", state}
    end
  end

  defp attach_leading_doc([first | rest], doc) when doc != "" do
    [attach_doc(first, doc) | rest]
  end

  defp attach_leading_doc(stmts, _doc), do: stmts

  # -- Decorator Attachment (@name before fn) --------------------------------

  defp parse_at(state) do
    token = peek(state)
    state = advance(state)

    name_token = peek(state)
    state = advance(state)
    dec_name = to_string(name_token.value)

    # Check if it's a call: @name(args)
    {args, state} =
      case peek(state) do
        %Token{type: :lparen} ->
          state = advance(state)
          {a, state} = parse_call_args(state)
          {a, state}

        _ ->
          {[], state}
      end

    state = skip_newlines(state)

    # Check if the next thing is a function definition -- if so, attach decorator
    case peek(state) do
      %Token{type: :keyword, value: kw} when kw in [:fn, :local] ->
        {fn_ast, state} = parse_expr(state, 0)
        fn_ast = attach_decorator(fn_ast, dec_name, args)
        {fn_ast, state}

      _ ->
        # Standalone decorator or property
        if args != [] do
          ast = {:decorator, [name: dec_name, line: token.line, col: token.col], args}
          {ast, state}
        else
          ast = {:property, [name: dec_name, line: token.line, col: token.col], dec_name}
          {ast, state}
        end
    end
  end

  defp attach_decorator(fn_ast, dec_name, args) do
    case fn_ast do
      {:function_def, meta, body} ->
        decoration =
          case dec_name do
            "extern" ->
              # @extern(:mod, :fun, arity) -> extern: {mod, fun, arity}
              extern_val =
                case args do
                  [m, f, a] -> {extract_literal_value(m), extract_literal_value(f), extract_literal_value(a)}
                  _ -> args
                end

              [extern: extern_val]

            _ ->
              [decorator: {String.to_atom(dec_name), args}]
          end

        {:function_def, meta ++ decoration, body}

      other ->
        other
    end
  end

  defp extract_literal_value({:literal, _, val}), do: val

  # `@extern(Elixir.Cure.FSM.Builtins, :f, 1)` parses the first argument
  # as a chain of attribute accesses rooted in a PascalCase variable.
  # Collapse that chain to an atom so codegen receives a literal atom.
  defp extract_literal_value({:attribute_access, _, _} = ast) do
    case attribute_access_to_dotted(ast) do
      nil -> ast
      name -> String.to_atom(name)
    end
  end

  defp extract_literal_value({:variable, _, name}) when is_binary(name) do
    case name do
      <<c, _::binary>> when c in ?A..?Z -> String.to_atom(name)
      _ -> name
    end
  end

  defp extract_literal_value(other), do: other

  defp attribute_access_to_dotted({:attribute_access, meta, [parent]}) do
    attr = Keyword.get(meta, :attribute)

    case attribute_access_to_dotted(parent) do
      nil -> nil
      path -> path <> "." <> to_string(attr)
    end
  end

  defp attribute_access_to_dotted({:variable, _, name}) when is_binary(name), do: name
  defp attribute_access_to_dotted(_), do: nil

  # -- Keyword unary (return, throw, yield, spawn) ---------------------------

  defp parse_keyword_unary(state, node_type) do
    token = peek(state)
    state = advance(state)
    {expr, state} = parse_expr(state, 0)
    ast = {node_type, [line: token.line, col: token.col], [expr]}
    {ast, state}
  end

  # -- Send ------------------------------------------------------------------

  defp parse_send(state) do
    token = peek(state)
    state = advance(state)
    {target, state} = parse_expr(state, 0)
    state = expect(state, :comma)
    {message, state} = parse_expr(state, 0)
    ast = {:function_call, [name: "send", line: token.line, col: token.col], [target, message]}
    {ast, state}
  end

  # -- Receive ---------------------------------------------------------------

  defp parse_receive(state) do
    token = peek(state)
    state = advance(state)
    state = skip_newlines(state)

    # Parse like match arms
    case peek(state) do
      %Token{type: :indent} ->
        state = advance(state)
        {arms, state} = parse_block_match_arms(state)
        state = expect_dedent(state)

        # Optional after timeout
        {timeout, state} =
          case peek(state) do
            %Token{type: :keyword, value: :after} ->
              state = advance(state)
              {timeout_expr, state} = parse_expr(state, 0)
              state = skip_newlines(state)
              {timeout_body, state} = parse_block(state)
              {{timeout_expr, timeout_body}, state}

            _ ->
              {nil, state}
          end

        meta = [line: token.line, col: token.col]
        meta = if timeout, do: Keyword.put(meta, :timeout, timeout), else: meta
        ast = {:async_operation, meta, arms}
        {ast, state}

      _ ->
        ast = {:async_operation, [line: token.line, col: token.col], []}
        {ast, state}
    end
  end

  # -- Try / Catch / Finally -------------------------------------------------

  defp parse_try(state) do
    token = peek(state)
    state = advance(state)
    state = skip_newlines(state)

    {try_body, state} = parse_block(state)
    state = skip_newlines(state)

    # catch clause
    {catch_arms, state} =
      case peek(state) do
        %Token{type: :keyword, value: :catch} ->
          state = advance(state)
          state = skip_newlines(state)

          case peek(state) do
            %Token{type: :indent} ->
              state = advance(state)
              {arms, state} = parse_block_match_arms(state)
              state = expect_dedent(state)
              {arms, state}

            _ ->
              {[], state}
          end

        _ ->
          {[], state}
      end

    state = skip_newlines(state)

    # finally clause
    {finally_body, state} =
      case peek(state) do
        %Token{type: :keyword, value: :finally} ->
          state = advance(state)
          state = skip_newlines(state)
          {body, state} = parse_block(state)
          {body, state}

        _ ->
          {nil, state}
      end

    children = [try_body | catch_arms]
    children = if finally_body, do: children ++ [finally_body], else: children
    ast = {:exception_handling, [line: token.line, col: token.col], children}
    {ast, state}
  end

  # -- Block Parsing ---------------------------------------------------------

  defp parse_block(state) do
    case peek(state) do
      %Token{type: :indent} ->
        token = peek(state)
        state = advance(state)
        {exprs, state} = parse_block_body(state)
        state = expect_dedent(state)

        case exprs do
          [single] -> {single, state}
          many -> {{:block, [line: token.line, col: token.col], many}, state}
        end

      _ ->
        # Single expression as body (no indent)
        parse_expr(state, 0)
    end
  end

  defp parse_block_body(state) do
    state = skip_newlines(state)
    parse_block_body(state, [])
  end

  defp parse_block_body(state, acc) do
    case peek(state) do
      %Token{type: type} when type in [:dedent, :eof] ->
        {Enum.reverse(acc), state}

      %Token{type: :doc_comment} ->
        {doc_text, state} = collect_doc_comments(state)
        state = skip_newlines(state)

        case peek(state) do
          %Token{type: type} when type in [:dedent, :eof] ->
            {Enum.reverse(acc), state}

          _ ->
            {expr, state} = parse_expr(state, 0)
            expr = attach_doc(expr, doc_text)
            state = skip_newlines(state)
            parse_block_body(state, [expr | acc])
        end

      _ ->
        {expr, state} = parse_expr(state, 0)
        state = skip_newlines(state)
        parse_block_body(state, [expr | acc])
    end
  end

  # Parse either a block (if indent follows) or a single expression
  defp parse_expr_or_block(state) do
    case peek(state) do
      %Token{type: :indent} -> parse_block(state)
      _ -> parse_expr(state, 0)
    end
  end

  # -- Comma-separated expressions -------------------------------------------

  defp parse_comma_exprs(state) do
    state = skip_newlines(state)

    case peek(state) do
      %Token{type: :comma} ->
        state = advance(state)
        state = skip_newlines(state)
        {expr, state} = parse_expr(state, 0)
        {rest, state} = parse_comma_exprs(state)
        {[expr | rest], state}

      _ ->
        {[], state}
    end
  end

  # -- Token Helpers ---------------------------------------------------------

  defp peek(%{tokens: tokens, pos: pos}) when pos >= length(tokens) do
    Token.new(:eof, nil, 1, 1)
  end

  defp peek(%{tokens: tokens, pos: pos}), do: Enum.at(tokens, pos)

  defp peek_at(%{tokens: tokens, pos: pos}, offset) do
    idx = pos + offset
    if idx >= 0 and idx < length(tokens), do: Enum.at(tokens, idx), else: nil
  end

  defp advance(state), do: %{state | pos: state.pos + 1}

  defp skip_newlines(state) do
    case peek(state) do
      %Token{type: :newline} -> skip_newlines(advance(state))
      _ -> state
    end
  end

  defp expect(state, expected_type) do
    token = peek(state)

    if token.type == expected_type do
      advance(state)
    else
      error = {:expected, expected_type, :got, token.type, token.line, token.col}
      add_error(state, error)
    end
  end

  defp expect_dedent(state) do
    case peek(state) do
      %Token{type: :dedent} -> advance(state)
      _ -> state
    end
  end

  defp add_error(state, error) do
    if state.emit_events do
      Events.emit(:parser, :error, error, Events.meta(state.file, 1))
    end

    %{state | errors: [error | state.errors]}
  end

  # -- Doc Comment Helpers -----------------------------------------------------

  defp collect_doc_comments(state) do
    collect_doc_comments(state, [])
  end

  defp collect_doc_comments(state, acc) do
    case peek(state) do
      %Token{type: :doc_comment, value: text} ->
        state = advance(state)
        state = skip_newlines(state)
        collect_doc_comments(state, [text | acc])

      _ ->
        doc = acc |> Enum.reverse() |> Enum.join("\n")
        {doc, state}
    end
  end

  defp attach_doc({type, meta, children}, doc) when is_list(meta) do
    {type, Keyword.put(meta, :doc, doc), children}
  end

  defp attach_doc(ast, _doc), do: ast
end
