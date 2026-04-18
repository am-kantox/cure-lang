defmodule Cure.Compiler.Lexer do
  @moduledoc """
  Lexer for the Cure programming language.

  Converts Cure source code into a flat list of tokens suitable for parsing.
  The lexer handles:

  - All Cure keywords (Section 3.3 of the syntax spec)
  - All operators (Section 3.4)
  - All literal forms (integers, floats, hex, binary, strings, atoms, booleans,
    nil, regex, char, binary/bytes literals)
  - Indentation tracking: emits `:indent` and `:dedent` tokens based on
    whitespace changes (spaces only; tabs are a lexer error)
  - String interpolation (`"hello \#{expr}"`)
  - Single-line comments (`#`)
  - Position tracking (line, column) on every token

  ## Pipeline Events

  The lexer emits the following events via `Cure.Pipeline.Events`:

  - `{:lexer, :token_produced, token, meta}` -- for each token produced
  - `{:lexer, :lex_complete, tokens, meta}` -- when lexing finishes successfully
  - `{:lexer, :error, error, meta}` -- on lexer errors

  ## Usage

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize("fn add(x: Int, y: Int) -> Int = x + y")
      {:error, reason} = Cure.Compiler.Lexer.tokenize("\\t invalid")
  """

  alias Cure.Compiler.Token
  alias Cure.Pipeline.Events

  # -- Keywords (Section 3.3) ------------------------------------------------

  @keywords ~w(
    mod fn let type rec proto impl fsm local use as
    match if elif else then for do
    in try catch finally throw return yield
    spawn send receive after
    when where and or not
    true false nil
    extern proof
  )a

  @keyword_strings Enum.map(@keywords, &Atom.to_string/1)

  # -- Lexer state -----------------------------------------------------------

  defstruct [
    :source,
    :file,
    pos: 0,
    line: 1,
    col: 1,
    tokens: [],
    indent_stack: [0],
    at_line_start: true,
    paren_depth: 0,
    fsm_transition_depth: 0,
    preserve_comments: false
  ]

  @type t :: %__MODULE__{}

  # -- Public API ------------------------------------------------------------

  @doc """
  Tokenize a Cure source string.

  Returns `{:ok, tokens}` on success or `{:error, reason}` on failure.
  The returned token list is in source order and ends with an `:eof` token.
  Appropriate `:dedent` tokens are emitted at the end to close all open
  indentation levels.

  ## Options

  - `:file` -- filename for error messages and event metadata (default: `"nofile"`)
  - `:emit_events` -- whether to emit pipeline events (default: `true`)
  - `:preserve_comments` -- when `true`, emit `:line_comment` tokens for plain
    `#` comments (v0.20.0+). Default `false` so existing pipelines see no
    change. Doc comments (`##`, `###`) are always preserved as `:doc_comment`
    tokens regardless of this flag.
  """
  @spec tokenize(String.t(), keyword()) :: {:ok, [Token.t()]} | {:error, term()}
  def tokenize(source, opts \\ []) do
    file = Keyword.get(opts, :file, "nofile")
    emit? = Keyword.get(opts, :emit_events, true)
    preserve? = Keyword.get(opts, :preserve_comments, false)

    state = %__MODULE__{source: source, file: file, preserve_comments: preserve?}

    case do_tokenize(state) do
      {:ok, state} ->
        # Close remaining indentation levels
        state = close_indents(state)
        tokens = Enum.reverse([Token.new(:eof, nil, state.line, state.col) | state.tokens])

        if emit? do
          Events.emit(:lexer, :lex_complete, tokens, Events.meta(file, state.line))
        end

        {:ok, tokens}

      {:error, reason, state} ->
        if emit? do
          Events.emit(:lexer, :error, reason, Events.meta(file, state.line))
        end

        {:error, reason}
    end
  end

  # -- Core loop -------------------------------------------------------------

  defp do_tokenize(%{source: source, pos: pos} = state) when pos >= byte_size(source) do
    {:ok, state}
  end

  defp do_tokenize(state) do
    case lex_next(state) do
      {:ok, state} -> do_tokenize(state)
      {:error, _reason, _state} = err -> err
    end
  catch
    {:error, _reason, _state} = err -> err
  end

  defp lex_next(%{at_line_start: true} = state) do
    lex_indentation(state)
  end

  defp lex_next(state) do
    case peek(state) do
      # Newline
      ?\n -> {:ok, handle_newline(state)}
      # Carriage return
      ?\r -> {:ok, advance(state, 1)}
      # Spaces (not at line start -> skip)
      ?\s -> {:ok, skip_spaces(state)}
      # Tab (error)
      ?\t -> {:error, {:tab_not_allowed, state.line, state.col}, state}
      # Comment
      ?# -> lex_comment_or_operator(state)
      # String
      ?" -> lex_string(state)
      # Char literal
      ?' -> lex_char(state)
      # Atom (symbol)
      ?: -> lex_atom_or_colon(state)
      # Regex sigil
      ?~ -> lex_regex(state)
      # Binary literal << >>
      ?< -> lex_angle_or_op(state)
      # Percent sigils: %[ %{
      ?% -> lex_percent(state)
      # Brackets
      ?( -> {:ok, emit_single(state, :lparen, "(", inc_paren: true)}
      ?) -> {:ok, emit_single(state, :rparen, ")", dec_paren: true)}
      ?[ -> {:ok, emit_single(state, :lbracket, "[")}
      ?] -> {:ok, emit_single(state, :rbracket, "]")}
      ?{ -> {:ok, emit_single(state, :lbrace, "{")}
      ?} -> {:ok, emit_single(state, :rbrace, "}")}
      ?, -> {:ok, emit_single(state, :comma, ",")}
      ?; -> {:ok, emit_single(state, :semicolon, ";")}
      # Operators and punctuation
      ?@ -> {:ok, emit_single(state, :at, "@")}
      ?_ -> lex_identifier(state)
      c when c in ?a..?z -> lex_identifier(state)
      c when c in ?A..?Z -> lex_identifier(state)
      c when c in ?0..?9 -> lex_number(state)
      ?+ -> lex_plus(state)
      ?- -> lex_minus(state)
      ?* -> lex_star(state)
      ?/ -> lex_slash(state)
      ?= -> lex_equal(state)
      ?! -> lex_bang(state)
      ?> -> lex_greater(state)
      ?| -> lex_pipe_or_bar(state)
      ?. -> lex_dot(state)
      ?^ -> {:ok, emit_single(state, :caret, "^")}
      _ -> {:error, {:unexpected_character, peek(state), state.line, state.col}, state}
    end
  end

  # -- Indentation -----------------------------------------------------------

  defp lex_indentation(state) do
    {indent, state} = measure_indent(state)

    # Skip blank lines and comment-only lines: they must not affect indentation.
    # If the next char after leading whitespace is a newline (or EOF), treat
    # the line as blank and keep `at_line_start: true` for the next line.
    case peek(state) do
      c when c in [?\n, ?\r, nil] ->
        # Blank line -- advance past the newline without emitting indent/dedent
        state =
          case c do
            ?\n ->
              %{state | pos: state.pos + 1, line: state.line + 1, col: 1}

            ?\r ->
              %{state | pos: state.pos + 1}

            nil ->
              state
          end

        {:ok, %{state | at_line_start: true}}

      ?# ->
        # Comment-only line -- consume comment or doc comment, then treat as blank.
        #
        # Emit any `:dedent` tokens *first* so a doc comment that sits at
        # a lower indent level than the previous block's contents binds to
        # the outer block. Without this, the token stream would put
        # `doc_comment` *before* `dedent`, which makes the parser treat
        # the comment as belonging to the inner (ending) block.
        state = maybe_emit_dedents_to(state, indent)

        cond do
          # `###` fenced multi-line doc comment
          peek_at(state, 1) == ?# and peek_at(state, 2) == ?# ->
            {:ok, state} = lex_fenced_doc(state)
            {:ok, %{state | at_line_start: true}}

          # `##` single-line doc comment
          peek_at(state, 1) == ?# ->
            start_col = state.col
            state = advance(state, 2)
            state = if peek(state) == ?\s, do: advance(state, 1), else: state
            {text, state} = consume_while(state, fn ch -> ch != ?\n end)
            token = Token.new(:doc_comment, text, state.line, start_col)
            maybe_emit_event(state, token)
            {:ok, %{state | tokens: [token | state.tokens], at_line_start: true}}

          # plain `#` comment
          true ->
            start_col = state.col
            state = advance(state, 1)
            state = if peek(state) == ?\s, do: advance(state, 1), else: state
            {text, state} = consume_while(state, fn ch -> ch != ?\n end)
            state = emit_line_comment_if_enabled(state, text, start_col)
            {:ok, %{state | at_line_start: true}}
        end

      _ ->
        [current | _] = state.indent_stack

        cond do
          indent > current ->
            state = push_indent(state, indent)
            {:ok, %{state | at_line_start: false}}

          indent < current ->
            state = pop_indents(state, indent)
            {:ok, %{state | at_line_start: false}}

          true ->
            {:ok, %{state | at_line_start: false}}
        end
    end
  end

  defp measure_indent(state) do
    measure_indent(state, 0)
  end

  defp measure_indent(state, acc) do
    case peek(state) do
      ?\s -> measure_indent(advance(state, 1), acc + 1)
      ?\t -> throw({:error, {:tab_not_allowed, state.line, state.col}, state})
      _ -> {acc, state}
    end
  end

  defp push_indent(state, indent) do
    token = Token.new(:indent, indent, state.line, 1)
    maybe_emit_event(state, token)
    %{state | indent_stack: [indent | state.indent_stack], tokens: [token | state.tokens]}
  end

  defp pop_indents(%{indent_stack: [current | rest]} = state, target) when current > target do
    token = Token.new(:dedent, current, state.line, 1)
    maybe_emit_event(state, token)
    state = %{state | indent_stack: rest, tokens: [token | state.tokens]}
    pop_indents(state, target)
  end

  defp pop_indents(state, _target), do: state

  # Emit any needed `:dedent` tokens so the current indent stack top is
  # `<= target`. Used when a comment-only line reduces the effective
  # indentation before we produce any content for that line.
  defp maybe_emit_dedents_to(%{indent_stack: [current | _]} = state, target)
       when current > target do
    pop_indents(state, target)
  end

  defp maybe_emit_dedents_to(state, _target), do: state

  defp close_indents(%{indent_stack: [0]} = state), do: state

  defp close_indents(%{indent_stack: [level | rest]} = state) when level > 0 do
    token = Token.new(:dedent, level, state.line, state.col)
    state = %{state | indent_stack: rest, tokens: [token | state.tokens]}
    close_indents(state)
  end

  defp close_indents(state), do: state

  # -- Newlines --------------------------------------------------------------

  defp handle_newline(state) do
    # Don't emit newline tokens when inside parens/brackets/braces
    if state.paren_depth > 0 do
      state |> advance(1) |> Map.put(:line, state.line + 1) |> Map.put(:col, 1)
    else
      token = Token.new(:newline, "\n", state.line, state.col)
      maybe_emit_event(state, token)

      %{state | tokens: [token | state.tokens]}
      |> advance(1)
      |> Map.put(:line, state.line + 1)
      |> Map.put(:col, 1)
      |> Map.put(:at_line_start, true)
    end
  end

  # -- Comments --------------------------------------------------------------

  defp lex_comment_or_operator(state) do
    # `#` introduces a comment. There are three flavours:
    #
    #   #         plain line comment
    #   ##        single-line doc comment (back-compat, one per line)
    #   ###...### fenced multi-line doc comment (v0.17.0+)
    #
    # The fenced form is preferred because it sidesteps a long-standing
    # parser ambiguity between `##` lines and multi-clause function
    # definitions, and because multi-line prose reads better without
    # having to prefix every line.
    cond do
      # ### ... ### -- fenced doc comment
      peek_at(state, 1) == ?# and peek_at(state, 2) == ?# ->
        lex_fenced_doc(state)

      # ## single-line doc comment
      peek_at(state, 1) == ?# ->
        start_col = state.col
        state = advance(state, 2)
        state = if peek(state) == ?\s, do: advance(state, 1), else: state
        {text, state} = consume_while(state, fn c -> c != ?\n end)
        token = Token.new(:doc_comment, text, state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]}}

      # plain `#` comment
      true ->
        start_col = state.col
        state = advance(state, 1)
        state = if peek(state) == ?\s, do: advance(state, 1), else: state
        {text, state} = consume_while(state, fn c -> c != ?\n end)
        state = emit_line_comment_if_enabled(state, text, start_col)
        {:ok, state}
    end
  end

  # Emit a `:line_comment` token for a plain `#` comment when preservation
  # is enabled. The token carries the trimmed comment body (without the
  # leading `# `), so consumers can re-render comments without having to
  # recover the prefix heuristically.
  defp emit_line_comment_if_enabled(%{preserve_comments: true} = state, text, start_col) do
    token = Token.new(:line_comment, text, state.line, start_col)
    maybe_emit_event(state, token)
    %{state | tokens: [token | state.tokens]}
  end

  defp emit_line_comment_if_enabled(state, _text, _start_col), do: state

  # Consume a `###\n...\n###` block and emit a single `:doc_comment` token.
  #
  # The opening `###` must be followed by either a newline or optional
  # whitespace and then a newline. Everything up to the next line that
  # consists of (whitespace + `###` + optional trailing content) is
  # collected as the doc body. Leading whitespace common to every body
  # line is stripped.
  defp lex_fenced_doc(state) do
    start_line = state.line
    start_col = state.col

    # Consume the opening ###.
    state = advance(state, 3)

    # Consume any `### some trailing text` on the opening line.
    {opening_tail, state} = consume_while(state, fn c -> c != ?\n end)

    # Step over the newline that ends the opening line.
    state =
      case peek(state) do
        ?\n ->
          state
          |> advance(1)
          |> Map.put(:line, state.line + 1)
          |> Map.put(:col, 1)

        _ ->
          state
      end

    {body_lines, state} = collect_fenced_lines(state, [])

    text =
      body_lines
      |> strip_common_indent()
      |> Enum.join("\n")
      |> prepend_opening_tail(opening_tail)

    token = Token.new(:doc_comment, text, start_line, start_col)
    maybe_emit_event(state, token)
    {:ok, %{state | tokens: [token | state.tokens]}}
  end

  defp collect_fenced_lines(state, acc) do
    cond do
      peek(state) == nil ->
        {Enum.reverse(acc), state}

      fence_close_line?(state) ->
        state = consume_fence_close(state)
        {Enum.reverse(acc), state}

      true ->
        {line, state} = consume_while(state, fn c -> c != ?\n end)

        state =
          case peek(state) do
            ?\n ->
              state
              |> advance(1)
              |> Map.put(:line, state.line + 1)
              |> Map.put(:col, 1)

            _ ->
              state
          end

        collect_fenced_lines(state, [line | acc])
    end
  end

  # True when the current position starts a line of the shape
  # `<whitespace>* ### <anything>*<newline or eof>`.
  defp fence_close_line?(state) do
    {_spaces, offset} = count_leading_spaces(state, 0)
    a = peek_at(state, offset)
    b = peek_at(state, offset + 1)
    c = peek_at(state, offset + 2)
    a == ?# and b == ?# and c == ?#
  end

  defp count_leading_spaces(state, offset) do
    case peek_at(state, offset) do
      ?\s -> count_leading_spaces(state, offset + 1)
      _ -> {offset, offset}
    end
  end

  defp consume_fence_close(state) do
    {_spaces, state} = consume_while(state, fn c -> c == ?\s end)
    # Advance past the three #s.
    state = advance(state, 3)
    # Consume any trailing content up to newline.
    {_trailing, state} = consume_while(state, fn c -> c != ?\n end)

    case peek(state) do
      ?\n ->
        state
        |> advance(1)
        |> Map.put(:line, state.line + 1)
        |> Map.put(:col, 1)

      _ ->
        state
    end
  end

  defp strip_common_indent([]), do: []

  defp strip_common_indent(lines) do
    non_blank = Enum.reject(lines, fn l -> String.trim(l) == "" end)

    indent =
      case non_blank do
        [] -> 0
        _ -> Enum.map(non_blank, &leading_space_count/1) |> Enum.min()
      end

    Enum.map(lines, fn l ->
      if String.length(l) >= indent, do: String.slice(l, indent..-1//1), else: l
    end)
  end

  defp leading_space_count(line) do
    line
    |> String.graphemes()
    |> Enum.take_while(fn g -> g == " " end)
    |> length()
  end

  defp prepend_opening_tail(body, tail) do
    trimmed = String.trim(tail)
    if trimmed == "", do: body, else: trimmed <> "\n" <> body
  end

  # -- Identifiers & keywords -----------------------------------------------

  defp lex_identifier(state) do
    start_col = state.col

    {word, state} =
      consume_while(state, fn c ->
        c in ?a..?z or c in ?A..?Z or c in ?0..?9 or c == ?_
      end)

    # Inside FSM transition bodies, allow trailing ! or ? on identifiers
    # to support determined (event!) and soft (event?) event suffixes.
    # Everywhere else, allow a trailing `?` for predicate-style names
    # (Elixir convention, e.g. `is_empty?`, `even?`). `!` is reserved for
    # effect annotations and FSM hard events.
    {word, state} =
      cond do
        state.fsm_transition_depth > 0 and word not in @keyword_strings ->
          case peek(state) do
            c when c in [?!, ??] ->
              {word <> <<c::utf8>>, advance(state, 1)}

            _ ->
              {word, state}
          end

        word not in @keyword_strings and peek(state) == ?? ->
          # `?` immediately followed by an identifier-starter is a *hole*
          # prefix (`?name`), so only consume the `?` when it is a
          # proper suffix (followed by something that can't begin a
          # new identifier on its own on this side).
          next = peek_at(state, 1)

          if next in ?a..?z or next in ?A..?Z or next == ?_ do
            {word, state}
          else
            {word <> "?", advance(state, 1)}
          end

        true ->
          {word, state}
      end

    {type, value} =
      if word in @keyword_strings do
        kw = String.to_atom(word)

        case kw do
          true -> {:bool, true}
          false -> {:bool, false}
          nil -> {nil, nil}
          :and -> {:and_op, :and}
          :or -> {:or_op, :or}
          :not -> {:not_op, :not}
          other -> {:keyword, other}
        end
      else
        {:identifier, word}
      end

    token = Token.new(type, value, state.line, start_col)
    maybe_emit_event(state, token)
    {:ok, %{state | tokens: [token | state.tokens]}}
  end

  # -- Numbers ---------------------------------------------------------------

  defp lex_number(state) do
    start_col = state.col

    case peek(state, 2) do
      "0x" -> lex_hex(state, start_col)
      "0b" -> lex_binary_int(state, start_col)
      _ -> lex_decimal(state, start_col)
    end
  end

  defp lex_hex(state, start_col) do
    state = advance(state, 2)

    {digits, state} =
      consume_while(state, fn c ->
        c in ?0..?9 or c in ?a..?f or c in ?A..?F or c == ?_
      end)

    if digits == "" do
      {:error, {:invalid_hex_literal, state.line, start_col}, state}
    else
      clean = String.replace(digits, "_", "")
      value = String.to_integer(clean, 16)
      token = Token.new(:integer, value, state.line, start_col)
      maybe_emit_event(state, token)
      {:ok, %{state | tokens: [token | state.tokens]}}
    end
  end

  defp lex_binary_int(state, start_col) do
    state = advance(state, 2)

    {digits, state} =
      consume_while(state, fn c ->
        c in [?0, ?1, ?_]
      end)

    if digits == "" do
      {:error, {:invalid_binary_literal, state.line, start_col}, state}
    else
      clean = String.replace(digits, "_", "")
      value = String.to_integer(clean, 2)
      token = Token.new(:integer, value, state.line, start_col)
      maybe_emit_event(state, token)
      {:ok, %{state | tokens: [token | state.tokens]}}
    end
  end

  defp lex_decimal(state, start_col) do
    {int_part, state} = consume_while(state, fn c -> c in ?0..?9 or c == ?_ end)

    cond do
      # Float: digits.digits or digits.digitseN
      peek(state) == ?. and peek_at(state, 1) in ?0..?9 ->
        state = advance(state, 1)
        {frac_part, state} = consume_while(state, fn c -> c in ?0..?9 or c == ?_ end)
        {exp_part, state} = lex_exponent(state)
        raw = "#{int_part}.#{frac_part}#{exp_part}" |> String.replace("_", "")
        value = String.to_float(raw)
        token = Token.new(:float, value, state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]}}

      # Scientific notation without dot: 1e3
      peek(state) in [?e, ?E] ->
        {exp_part, state} = lex_exponent(state)
        raw = "#{int_part}.0#{exp_part}" |> String.replace("_", "")
        value = String.to_float(raw)
        token = Token.new(:float, value, state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]}}

      true ->
        clean = String.replace(int_part, "_", "")
        value = String.to_integer(clean)
        token = Token.new(:integer, value, state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]}}
    end
  end

  defp lex_exponent(state) do
    case peek(state) do
      c when c in [?e, ?E] ->
        state = advance(state, 1)

        {sign, state} =
          case peek(state) do
            ?+ -> {"+", advance(state, 1)}
            ?- -> {"-", advance(state, 1)}
            _ -> {"", state}
          end

        {digits, state} = consume_while(state, fn c -> c in ?0..?9 end)
        {"e#{sign}#{digits}", state}

      _ ->
        {"", state}
    end
  end

  # -- Strings ---------------------------------------------------------------

  defp lex_string(state) do
    start_col = state.col
    state = advance(state, 1)
    lex_string_body(state, start_col, [])
  end

  defp lex_string_body(state, start_col, acc) do
    case peek(state) do
      nil ->
        {:error, {:unterminated_string, state.line, start_col}, state}

      ?" ->
        state = advance(state, 1)
        parts = Enum.reverse(acc)

        if Enum.all?(parts, &is_binary/1) do
          # Plain string, no interpolation
          value = IO.iodata_to_binary(parts)
          token = Token.new(:string, value, state.line, start_col)
          maybe_emit_event(state, token)
          {:ok, %{state | tokens: [token | state.tokens]}}
        else
          # String with interpolation parts
          normalized = normalize_string_parts(parts)
          token = Token.new(:string_interpolation, normalized, state.line, start_col)
          maybe_emit_event(state, token)
          {:ok, %{state | tokens: [token | state.tokens]}}
        end

      ?\\ ->
        state = advance(state, 1)

        case peek(state) do
          ?n -> lex_string_body(advance(state, 1), start_col, ["\n" | acc])
          ?t -> lex_string_body(advance(state, 1), start_col, ["\t" | acc])
          ?\\ -> lex_string_body(advance(state, 1), start_col, ["\\" | acc])
          ?" -> lex_string_body(advance(state, 1), start_col, ["\"" | acc])
          ?# -> lex_string_body(advance(state, 1), start_col, ["#" | acc])
          _ -> lex_string_body(state, start_col, ["\\" | acc])
        end

      ?# ->
        if peek_at(state, 1) == ?{ do
          # String interpolation
          state = advance(state, 2)
          {expr_tokens, state} = lex_interpolation_expr(state, 0)
          lex_string_body(state, start_col, [{:expr, expr_tokens} | acc])
        else
          state2 = advance(state, 1)
          lex_string_body(state2, start_col, ["#" | acc])
        end

      c ->
        state = advance(state, 1)
        lex_string_body(state, start_col, [<<c::utf8>> | acc])
    end
  end

  defp lex_interpolation_expr(state, depth) do
    case peek(state) do
      nil ->
        {[], state}

      ?} when depth == 0 ->
        {[], advance(state, 1)}

      ?{ ->
        token = Token.new(:lbrace, "{", state.line, state.col)
        {rest, state} = lex_interpolation_expr(advance(state, 1), depth + 1)
        {[token | rest], state}

      ?} ->
        token = Token.new(:rbrace, "}", state.line, state.col)
        {rest, state} = lex_interpolation_expr(advance(state, 1), depth - 1)
        {[token | rest], state}

      _ ->
        # Tokenize one token inside interpolation, then continue
        inner_state = %{state | tokens: [], paren_depth: 0}

        case lex_next(inner_state) do
          {:ok, inner_state} ->
            produced = Enum.reverse(inner_state.tokens)

            next_state = %{inner_state | tokens: state.tokens, paren_depth: state.paren_depth}
            {rest, final_state} = lex_interpolation_expr(next_state, depth)
            {produced ++ rest, final_state}

          {:error, _reason, err_state} ->
            {[], err_state}
        end
    end
  end

  defp normalize_string_parts(parts) do
    # Merge consecutive binary parts, keep {:expr, tokens} as-is
    parts
    |> Enum.reduce([], fn
      part, [{:string_part, prev} | rest] when is_binary(part) ->
        [{:string_part, prev <> part} | rest]

      part, acc when is_binary(part) ->
        [{:string_part, part} | acc]

      {:expr, tokens}, acc ->
        [{:expr, tokens} | acc]
    end)
    |> Enum.reverse()
  end

  # -- Char literal ----------------------------------------------------------

  defp lex_char(state) do
    start_col = state.col
    # Advance past opening '
    state = advance(state, 1)

    case peek(state) do
      ?\\ ->
        state = advance(state, 1)

        {value, state} =
          case peek(state) do
            ?n -> {?\n, advance(state, 1)}
            ?t -> {?\t, advance(state, 1)}
            ?\\ -> {?\\, advance(state, 1)}
            ?' -> {?', advance(state, 1)}
            ?0 -> {0, advance(state, 1)}
            c -> {c, advance(state, 1)}
          end

        # Expect closing '
        case peek(state) do
          ?' ->
            state = advance(state, 1)
            token = Token.new(:char, value, state.line, start_col)
            maybe_emit_event(state, token)
            {:ok, %{state | tokens: [token | state.tokens]}}

          _ ->
            {:error, {:unterminated_char, state.line, start_col}, state}
        end

      nil ->
        {:error, {:unterminated_char, state.line, start_col}, state}

      c ->
        state = advance(state, 1)

        # Expect closing '
        case peek(state) do
          ?' ->
            state = advance(state, 1)
            token = Token.new(:char, c, state.line, start_col)
            maybe_emit_event(state, token)
            {:ok, %{state | tokens: [token | state.tokens]}}

          _ ->
            {:error, {:unterminated_char, state.line, start_col}, state}
        end
    end
  end

  # -- Atom / colon ----------------------------------------------------------

  defp lex_atom_or_colon(state) do
    start_col = state.col
    next = peek_at(state, 1)

    cond do
      next in ?a..?z or next in ?A..?Z or next == ?_ ->
        state = advance(state, 1)

        {name, state} =
          consume_while(state, fn c ->
            c in ?a..?z or c in ?A..?Z or c in ?0..?9 or c == ?_
          end)

        # Allow trailing ? or ! for atoms
        {name, state} =
          if peek(state) in [??, ?!] do
            {name <> <<peek(state)::utf8>>, advance(state, 1)}
          else
            {name, state}
          end

        token = Token.new(:atom, String.to_atom(name), state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]}}

      # `::` is the binary-segment specifier operator introduced in
      # v0.20.0. It is distinct from `:` (type annotations) and from
      # `:atom` (symbol literals). Inside `<<...>>` it separates a
      # segment value from its specifier chain.
      next == ?: ->
        token = Token.new(:colon_colon, "::", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      true ->
        token = Token.new(:colon, ":", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}
    end
  end

  # -- Regex -----------------------------------------------------------------

  defp lex_regex(state) do
    start_col = state.col

    if peek_at(state, 1) == ?r and peek_at(state, 2) == ?/ do
      state = advance(state, 3)
      {body, state} = consume_while(state, fn c -> c != ?/ end)
      state = advance(state, 1)
      # Read flags
      {flags, state} = consume_while(state, fn c -> c in ?a..?z end)
      token = Token.new(:regex, {body, flags}, state.line, start_col)
      maybe_emit_event(state, token)
      {:ok, %{state | tokens: [token | state.tokens]}}
    else
      {:error, {:unexpected_character, ?~, state.line, state.col}, state}
    end
  end

  # -- Binary literal << >> --------------------------------------------------

  defp lex_angle_or_op(state) do
    start_col = state.col

    case {peek(state), peek_at(state, 1)} do
      {?<, ?<} ->
        token = Token.new(:binary_open, "<<", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      {?<, ?>} ->
        # String concat operator
        token = Token.new(:string_concat, "<>", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      {?<, ?=} ->
        token = Token.new(:lte, "<=", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      _ ->
        token = Token.new(:lt, "<", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}
    end
  end

  # -- Percent sigils: %[ and %{ ---------------------------------------------

  defp lex_percent(state) do
    start_col = state.col

    case peek_at(state, 1) do
      ?[ ->
        token = Token.new(:tuple_open, "%[", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      ?{ ->
        token = Token.new(:map_open, "%{", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      _ ->
        token = Token.new(:percent, "%", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}
    end
  end

  # -- Operators -------------------------------------------------------------

  defp lex_plus(state) do
    start_col = state.col

    if peek_at(state, 1) == ?= do
      token = Token.new(:plus_assign, "+=", state.line, start_col)
      maybe_emit_event(state, token)
      {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}
    else
      token = Token.new(:plus, "+", state.line, start_col)
      maybe_emit_event(state, token)
      {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}
    end
  end

  defp lex_minus(state) do
    start_col = state.col

    case peek_at(state, 1) do
      ?= ->
        token = Token.new(:minus_assign, "-=", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      ?> ->
        token = Token.new(:arrow, "->", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      ?- ->
        # FSM transition: --event--> or --event when guard-->
        lex_fsm_transition(state, start_col)

      _ ->
        token = Token.new(:minus, "-", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}
    end
  end

  defp lex_fsm_transition(state, start_col) do
    # FSM transition: --event--> or --event when guard-->
    # We emit: :transition_open (--), then let the parser handle the event name,
    # and :transition_close (-->)
    state = advance(state, 2)
    token = Token.new(:transition_open, "--", state.line, start_col)
    maybe_emit_event(state, token)
    state = %{state | tokens: [token | state.tokens], fsm_transition_depth: state.fsm_transition_depth + 1}

    # Now lex until we find -->
    lex_fsm_transition_body(state)
  end

  defp lex_fsm_transition_body(state) do
    case {peek(state), peek_at(state, 1), peek_at(state, 2)} do
      {?-, ?-, ?>} ->
        close_col = state.col
        state = advance(state, 3)
        token = Token.new(:transition_close, "-->", state.line, close_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens], fsm_transition_depth: max(state.fsm_transition_depth - 1, 0)}}

      {nil, _, _} ->
        {:error, {:unterminated_fsm_transition, state.line, state.col}, state}

      _ ->
        # Tokenize one token inside the transition
        case lex_next(state) do
          {:ok, state} -> lex_fsm_transition_body(state)
          error -> error
        end
    end
  end

  defp lex_star(state) do
    start_col = state.col

    if peek_at(state, 1) == ?= do
      token = Token.new(:star_assign, "*=", state.line, start_col)
      maybe_emit_event(state, token)
      {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}
    else
      token = Token.new(:star, "*", state.line, start_col)
      maybe_emit_event(state, token)
      {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}
    end
  end

  defp lex_slash(state) do
    start_col = state.col

    if peek_at(state, 1) == ?= do
      token = Token.new(:slash_assign, "/=", state.line, start_col)
      maybe_emit_event(state, token)
      {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}
    else
      token = Token.new(:slash, "/", state.line, start_col)
      maybe_emit_event(state, token)
      {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}
    end
  end

  defp lex_equal(state) do
    start_col = state.col

    case peek_at(state, 1) do
      ?= ->
        token = Token.new(:eq, "==", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      ?> ->
        token = Token.new(:fat_arrow, "=>", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      _ ->
        token = Token.new(:assign, "=", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}
    end
  end

  defp lex_bang(state) do
    start_col = state.col

    if peek_at(state, 1) == ?= do
      token = Token.new(:neq, "!=", state.line, start_col)
      maybe_emit_event(state, token)
      {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}
    else
      token = Token.new(:bang, "!", state.line, start_col)
      maybe_emit_event(state, token)
      {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}
    end
  end

  defp lex_greater(state) do
    start_col = state.col

    case peek_at(state, 1) do
      ?= ->
        token = Token.new(:gte, ">=", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      ?> ->
        token = Token.new(:binary_close, ">>", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      _ ->
        token = Token.new(:gt, ">", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}
    end
  end

  defp lex_pipe_or_bar(state) do
    start_col = state.col

    if peek_at(state, 1) == ?> do
      token = Token.new(:pipe, "|>", state.line, start_col)
      maybe_emit_event(state, token)
      {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}
    else
      token = Token.new(:bar, "|", state.line, start_col)
      maybe_emit_event(state, token)
      {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}
    end
  end

  defp lex_dot(state) do
    start_col = state.col

    case {peek_at(state, 1), peek_at(state, 2)} do
      {?., ?=} ->
        token = Token.new(:range_inclusive, "..=", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(3)}

      {?., _} ->
        token = Token.new(:range, "..", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(2)}

      _ ->
        token = Token.new(:dot, ".", state.line, start_col)
        maybe_emit_event(state, token)
        {:ok, %{state | tokens: [token | state.tokens]} |> advance(1)}
    end
  end

  # -- Helpers ---------------------------------------------------------------

  defp peek(%{source: source, pos: pos}) when pos >= byte_size(source), do: nil
  defp peek(%{source: source, pos: pos}), do: :binary.at(source, pos)

  defp peek_at(%{source: source, pos: pos}, offset) do
    at = pos + offset

    if at >= byte_size(source) do
      nil
    else
      :binary.at(source, at)
    end
  end

  defp peek(%{source: source, pos: pos}, len) do
    if pos + len > byte_size(source) do
      nil
    else
      binary_part(source, pos, len)
    end
  end

  defp advance(state, n) do
    %{state | pos: state.pos + n, col: state.col + n}
  end

  defp skip_spaces(state) do
    case peek(state) do
      ?\s -> skip_spaces(advance(state, 1))
      _ -> state
    end
  end

  defp consume_while(state, pred) do
    consume_while(state, pred, [])
  end

  defp consume_while(state, pred, acc) do
    case peek(state) do
      nil ->
        {IO.iodata_to_binary(Enum.reverse(acc)), state}

      c ->
        if pred.(c) do
          consume_while(advance(state, 1), pred, [<<c::utf8>> | acc])
        else
          {IO.iodata_to_binary(Enum.reverse(acc)), state}
        end
    end
  end

  defp emit_single(state, type, value, opts \\ []) do
    token = Token.new(type, value, state.line, state.col)
    maybe_emit_event(state, token)

    state = %{state | tokens: [token | state.tokens]}
    state = advance(state, String.length(value))

    state =
      if Keyword.get(opts, :inc_paren, false),
        do: %{state | paren_depth: state.paren_depth + 1},
        else: state

    state =
      if Keyword.get(opts, :dec_paren, false),
        do: %{state | paren_depth: max(state.paren_depth - 1, 0)},
        else: state

    state
  end

  defp maybe_emit_event(state, token) do
    Events.emit(:lexer, :token_produced, token, Events.meta(state.file, token.line))
  end
end
