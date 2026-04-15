defmodule Cure.Compiler.LexerTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Lexer
  alias Cure.Compiler.Token

  # Helper to extract token types (excluding :eof)
  defp types(tokens), do: tokens |> Enum.reject(&(&1.type == :eof)) |> Enum.map(& &1.type)

  # Helper to extract token values (excluding :eof)
  defp values(tokens), do: tokens |> Enum.reject(&(&1.type == :eof)) |> Enum.map(& &1.value)

  defp lex!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    tokens
  end

  # ── Keywords ──────────────────────────────────────────────────────────

  describe "keywords" do
    test "all Cure keywords are recognized" do
      keywords = ~w(mod fn let type rec proto impl fsm local use as
                    match if elif else then for do
                    in try catch finally throw return yield
                    spawn send receive after when where extern)

      for kw <- keywords do
        tokens = lex!(kw)
        assert [%Token{type: :keyword, value: val}, _eof] = tokens
        assert val == String.to_atom(kw)
      end
    end

    test "boolean literals are separate token types" do
      assert [%Token{type: :bool, value: true}, _] = lex!("true")
      assert [%Token{type: :bool, value: false}, _] = lex!("false")
    end

    test "nil literal" do
      assert [%Token{type: nil, value: nil}, _] = lex!("nil")
    end

    test "and, or, not are operator tokens" do
      assert [%Token{type: :and_op, value: :and}, _] = lex!("and")
      assert [%Token{type: :or_op, value: :or}, _] = lex!("or")
      assert [%Token{type: :not_op, value: :not}, _] = lex!("not")
    end

    test "identifiers that start like keywords but continue" do
      assert [%Token{type: :identifier, value: "function"}, _] = lex!("function")
      assert [%Token{type: :identifier, value: "letter"}, _] = lex!("letter")
      assert [%Token{type: :identifier, value: "modular"}, _] = lex!("modular")
    end
  end

  # ── Identifiers ──────────────────────────────────────────────────────

  describe "identifiers" do
    test "snake_case identifiers" do
      assert [%Token{type: :identifier, value: "my_var"}, _] = lex!("my_var")
    end

    test "PascalCase identifiers" do
      assert [%Token{type: :identifier, value: "MyModule"}, _] = lex!("MyModule")
    end

    test "underscore-prefixed identifiers" do
      assert [%Token{type: :identifier, value: "_unused"}, _] = lex!("_unused")
    end

    test "plain underscore (wildcard)" do
      assert [%Token{type: :identifier, value: "_"}, _] = lex!("_")
    end

    test "identifiers with digits" do
      assert [%Token{type: :identifier, value: "x1"}, _] = lex!("x1")
      assert [%Token{type: :identifier, value: "vec3d"}, _] = lex!("vec3d")
    end
  end

  # ── Number Literals ──────────────────────────────────────────────────

  describe "integers" do
    test "decimal integers" do
      assert [%Token{type: :integer, value: 42}, _] = lex!("42")
      assert [%Token{type: :integer, value: 0}, _] = lex!("0")
      assert [%Token{type: :integer, value: 1_000_000}, _] = lex!("1_000_000")
    end

    test "hex integers" do
      assert [%Token{type: :integer, value: 0xFF}, _] = lex!("0xFF")
      assert [%Token{type: :integer, value: 0xDEAD}, _] = lex!("0xDEAD")
    end

    test "binary integers" do
      assert [%Token{type: :integer, value: 0b1010}, _] = lex!("0b1010")
      assert [%Token{type: :integer, value: 0b1111_0000}, _] = lex!("0b1111_0000")
    end
  end

  describe "floats" do
    test "simple floats" do
      assert [%Token{type: :float, value: 3.14}, _] = lex!("3.14")
      assert [%Token{type: :float, value: 0.5}, _] = lex!("0.5")
    end

    test "scientific notation" do
      assert [%Token{type: :float, value: 1.0e-3}, _] = lex!("1.0e-3")
      assert [%Token{type: :float, value: 2.5e10}, _] = lex!("2.5e10")
    end

    test "integer with exponent becomes float" do
      tokens = lex!("1e3")
      assert [%Token{type: :float, value: v}, _] = tokens
      assert v == 1.0e3
    end
  end

  # ── String Literals ──────────────────────────────────────────────────

  describe "strings" do
    test "simple string" do
      assert [%Token{type: :string, value: "hello"}, _] = lex!(~s("hello"))
    end

    test "string with escape sequences" do
      tokens = lex!(~s("line1\\nline2"))
      assert [%Token{type: :string, value: "line1\nline2"}, _] = tokens
    end

    test "string with escaped quote" do
      tokens = lex!(~s("say \\"hi\\""))
      assert [%Token{type: :string, value: ~s(say "hi")}, _] = tokens
    end

    test "empty string" do
      assert [%Token{type: :string, value: ""}, _] = lex!(~s(""))
    end

    test "unterminated string returns error" do
      assert {:error, {:unterminated_string, 1, 1}} = Lexer.tokenize(~s("hello), emit_events: false)
    end
  end

  describe "string interpolation" do
    test "simple interpolation" do
      tokens = lex!(~s("hello \#{name}"))
      assert [%Token{type: :string_interpolation, value: parts}, _] = tokens
      assert [{:string_part, "hello "}, {:expr, expr_tokens}] = parts
      assert [%Token{type: :identifier, value: "name"}] = expr_tokens
    end

    test "interpolation with expression" do
      tokens = lex!(~s("result: \#{x + 1}"))
      assert [%Token{type: :string_interpolation, value: parts}, _] = tokens
      assert [{:string_part, "result: "}, {:expr, expr_tokens}] = parts
      expr_types = Enum.map(expr_tokens, & &1.type)
      assert expr_types == [:identifier, :plus, :integer]
    end

    test "string with no interpolation despite hash" do
      tokens = lex!(~s("hello # world"))
      assert [%Token{type: :string, value: "hello # world"}, _] = tokens
    end
  end

  # ── Atom / Symbol Literals ──────────────────────────────────────────

  describe "atoms" do
    test "simple atoms" do
      assert [%Token{type: :atom, value: :ok}, _] = lex!(":ok")
      assert [%Token{type: :atom, value: :error}, _] = lex!(":error")
    end

    test "atom with underscore" do
      assert [%Token{type: :atom, value: :my_atom}, _] = lex!(":my_atom")
    end

    test "colon not followed by identifier is a colon token" do
      tokens = lex!("x: Int")
      assert [:identifier, :colon, :identifier] = types(tokens)
    end
  end

  # ── Char Literals ────────────────────────────────────────────────────

  describe "char literals" do
    test "simple char" do
      assert [%Token{type: :char, value: ?c}, _] = lex!("'c'")
    end

    test "escaped char" do
      assert [%Token{type: :char, value: ?\n}, _] = lex!("'\\n'")
      assert [%Token{type: :char, value: ?\\}, _] = lex!("'\\\\'")
    end
  end

  # ── Regex Literals ───────────────────────────────────────────────────

  describe "regex literals" do
    test "simple regex" do
      assert [%Token{type: :regex, value: {"[a-z]+", "i"}}, _] = lex!("~r/[a-z]+/i")
    end

    test "regex without flags" do
      assert [%Token{type: :regex, value: {"\\d+", ""}}, _] = lex!("~r/\\d+/")
    end
  end

  # ── Operators ────────────────────────────────────────────────────────

  describe "operators" do
    test "arithmetic operators" do
      assert [:plus, :minus, :star, :slash, :percent] =
               types(lex!("+ - * / %"))
    end

    test "comparison operators" do
      assert [:eq, :neq, :lt, :gt, :lte, :gte] =
               types(lex!("== != < > <= >="))
    end

    test "assignment operators" do
      assert [:assign, :plus_assign, :minus_assign, :star_assign, :slash_assign] =
               types(lex!("= += -= *= /="))
    end

    test "arrow and fat arrow" do
      assert [:arrow, :fat_arrow] = types(lex!("-> =>"))
    end

    test "pipe operator" do
      assert [:pipe] = types(lex!("|>"))
    end

    test "bar (cons / sum separator)" do
      assert [:bar] = types(lex!("|"))
    end

    test "dot and range operators" do
      assert [:dot] = types(lex!("."))
      assert [:range] = types(lex!(".."))
      assert [:range_inclusive] = types(lex!("..="))
    end

    test "string concatenation" do
      assert [:string_concat] = types(lex!("<>"))
    end

    test "binary open/close" do
      assert [:binary_open, :binary_close] = types(lex!("<< >>"))
    end
  end

  # ── Collection Sigils ────────────────────────────────────────────────

  describe "collection sigils" do
    test "tuple sigil %[" do
      tokens = lex!("%[1, 2]")
      assert [:tuple_open, :integer, :comma, :integer, :rbracket] = types(tokens)
    end

    test "map sigil %{" do
      tokens = lex!("%{a: 1}")
      assert [:map_open, :identifier, :colon, :integer, :rbrace] = types(tokens)
    end
  end

  # ── Brackets and Punctuation ────────────────────────────────────────

  describe "brackets and punctuation" do
    test "all bracket types" do
      tokens = lex!("( ) [ ] { }")
      assert [:lparen, :rparen, :lbracket, :rbracket, :lbrace, :rbrace] = types(tokens)
    end

    test "comma and semicolon" do
      assert [:comma, :semicolon] = types(lex!(", ;"))
    end

    test "at sign (decorator)" do
      assert [:at] = types(lex!("@"))
    end

    test "caret" do
      assert [:caret] = types(lex!("^"))
    end
  end

  # ── Comments ─────────────────────────────────────────────────────────

  describe "comments" do
    test "comments are skipped" do
      tokens = lex!("x # this is a comment\ny")
      assert ["x", "\n", "y"] = values(tokens)
    end

    test "comment-only line produces no tokens" do
      tokens = lex!("# just a comment")
      assert [:eof] = Enum.map(tokens, & &1.type)
    end
  end

  # ── Indentation ──────────────────────────────────────────────────────

  describe "indentation" do
    test "indent and dedent tokens are emitted" do
      source = "x\n  y\nz"
      tokens = lex!(source)
      token_types = types(tokens)
      assert :indent in token_types
      assert :dedent in token_types
    end

    test "multiple indent levels" do
      source = "a\n  b\n    c\nd"
      tokens = lex!(source)
      indents = tokens |> Enum.filter(&(&1.type == :indent)) |> length()
      dedents = tokens |> Enum.filter(&(&1.type == :dedent)) |> length()
      assert indents == 2
      assert dedents == 2
    end

    test "remaining indentation closed at EOF" do
      source = "a\n  b\n    c"
      tokens = lex!(source)
      dedents = tokens |> Enum.filter(&(&1.type == :dedent)) |> length()
      assert dedents == 2
    end

    test "tabs are rejected" do
      assert {:error, {:tab_not_allowed, _, _}} = Lexer.tokenize("\tx", emit_events: false)
    end
  end

  # ── Newline Suppression in Parens ───────────────────────────────────

  describe "newline suppression" do
    test "newlines inside parentheses are suppressed" do
      source = "f(\n  x,\n  y\n)"
      tokens = lex!(source)
      refute :newline in types(tokens)
    end
  end

  # ── FSM Transitions ──────────────────────────────────────────────────

  describe "FSM transitions" do
    test "simple transition --event-->" do
      tokens = lex!("--timer-->")
      token_types = types(tokens)
      assert :transition_open in token_types
      assert :transition_close in token_types
      assert :identifier in token_types
    end

    test "guarded transition --event when guard-->" do
      tokens = lex!("--increment when value < 100-->")
      token_types = types(tokens)
      assert :transition_open in token_types
      assert :transition_close in token_types
      # when
      assert :keyword in token_types
    end
  end

  # ── Position Tracking ───────────────────────────────────────────────

  describe "position tracking" do
    test "first token starts at line 1, col 1" do
      [token | _] = lex!("hello")
      assert token.line == 1
      assert token.col == 1
    end

    test "tokens on second line have correct line number" do
      tokens = lex!("a\nb")
      b = Enum.find(tokens, &(&1.value == "b"))
      assert b.line == 2
    end
  end

  # ── Complete Expression ──────────────────────────────────────────────

  describe "complete expressions" do
    test "function definition signature" do
      source = "fn add(x: Int, y: Int) -> Int = x + y"
      {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
      token_types = types(tokens)

      # fn
      assert :keyword in token_types
      # add, x, y, Int
      assert :identifier in token_types
      assert :lparen in token_types
      assert :rparen in token_types
      assert :colon in token_types
      # ->
      assert :arrow in token_types
      # =
      assert :assign in token_types
      assert :plus in token_types
    end

    test "list with cons" do
      tokens = lex!("[head | tail]")
      assert [:lbracket, :identifier, :bar, :identifier, :rbracket] = types(tokens)
    end

    test "pipe chain" do
      tokens = lex!("x |> f |> g")
      assert [:identifier, :pipe, :identifier, :pipe, :identifier] = types(tokens)
    end
  end

  # ── Pipeline Events ──────────────────────────────────────────────────

  describe "pipeline events" do
    test "lex_complete event is emitted on success" do
      Cure.Pipeline.Events.subscribe(:lexer, :lex_complete)
      Lexer.tokenize("42", emit_events: true)

      assert_receive {Cure.Pipeline.Events, :lexer, :lex_complete, tokens, _meta}
      assert is_list(tokens)
    end

    test "error event is emitted on failure" do
      Cure.Pipeline.Events.subscribe(:lexer, :error)
      Lexer.tokenize("\t", emit_events: true)

      assert_receive {Cure.Pipeline.Events, :lexer, :error, {:tab_not_allowed, _, _}, _meta}
    end
  end
end
