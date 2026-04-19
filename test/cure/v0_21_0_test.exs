defmodule Cure.V0_21_0Test do
  @moduledoc """
  Integration tests for v0.21.0 "Through the Segments".

  Exercises the end-to-end compile pipeline for every v0.21.0 surface:

    * multi-line `type` ADT declarations (both leading-`|` and
      continuation-`|` forms);
    * ADT constructor payloads carrying function types;
    * in-place destructuring in `let` (ADT, tuple, list, record, binary);
    * binary destructuring in `match`, function heads, and `let`;
    * algebra formatter as the default `cure fmt`;
    * `@derive` extensions (Functor, Monoid, JSON);
    * new error-code explanations (E031-E034).

  Every test compiles a self-contained Cure source through
  `Cure.Compiler.compile_string/2` with an isolated output directory,
  so state from earlier tests never leaks into later ones.
  """
  use ExUnit.Case, async: true

  alias Cure.Compiler
  alias Cure.Compiler.{Errors, Lexer, Parser}
  alias Cure.Types.{Derive, PatternChecker}

  @out_dir "_build/cure/v0_21_0_test_out"

  setup_all do
    File.mkdir_p!(@out_dir)
    :ok
  end

  # -- Section 3: multi-line ADT declarations --------------------------------

  describe "multi-line ADT declarations" do
    test "leading `|` on every continuation line parses" do
      source = """
      mod M
        type Shape =
          | Circle(Int)
          | Square(Int)
          | Triangle(Int, Int, Int)
      """

      {:ok, ast} = tokenize_parse(source)
      assert {:container, _mod_meta, [{:container, type_meta, variants}]} = ast
      assert Keyword.get(type_meta, :container_type) == :enum
      assert Keyword.get(type_meta, :name) == "Shape"
      assert [_, _, _] = variants
    end

    test "no leading `|`, continuation `|` still parses" do
      source = """
      mod M
        type Shape =
          Circle(Int)
          | Square(Int)
      """

      {:ok, ast} = tokenize_parse(source)
      assert {:container, _, [{:container, _type_meta, [_, _]}]} = ast
    end

    test "E033 is registered" do
      assert {:ok, text} = Errors.explain("E033")
      assert text =~ "Multi-line Type Layout Invalid"
    end
  end

  # -- Section 2: ADT function-type payloads ---------------------------------

  describe "ADT function-type payloads" do
    test "bare arrow in constructor payload compiles end-to-end" do
      source = """
      mod M
        type Callback = On(Int -> Int) | Off

        fn apply_cb(cb: Callback, x: Int) -> Int =
          match cb
            On(f) -> f(x)
            Off -> x
      """

      assert {:ok, _mod, _warnings} = compile(source)
    end

    test "paren-grouped arrow in constructor payload compiles end-to-end" do
      source = """
      mod M
        type Transform = Morph((Int, Int) -> Int) | Id

        fn apply_t(t: Transform, a: Int, b: Int) -> Int =
          match t
            Morph(f) -> f(a, b)
            Id -> a
      """

      assert {:ok, _mod, _warnings} = compile(source)
    end

    test "E032 is registered" do
      assert {:ok, text} = Errors.explain("E032")
      assert text =~ "Function Type Payload Invalid"
    end
  end

  # -- Section 4: let destructuring ------------------------------------------

  describe "let destructuring" do
    test "let Ok(x) binds x in the let body" do
      source = """
      mod M
        fn f() -> Int =
          let Ok(x) = Ok(1)
          x
      """

      assert {:ok, _mod, _warnings} = compile(source)
    end

    test "let %[a, b] binds both components" do
      source = """
      mod M
        fn f() -> Int =
          let %[a, b] = %[1, 2]
          a + b
      """

      assert {:ok, _mod, _warnings} = compile(source)
    end

    test "let [h | _t] binds head" do
      source = """
      mod M
        fn f() -> Int =
          let [h | _t] = [1, 2, 3]
          h
      """

      assert {:ok, _mod, _warnings} = compile(source)
    end

    test "let Point{x, y} punning binds fields" do
      source = """
      mod M
        rec Point
          x: Int
          y: Int
        fn make() -> Point = Point{x: 1, y: 2}
        fn f() -> Int =
          let Point{x, y} = make()
          x + y
      """

      assert {:ok, _mod, _warnings} = compile(source)
    end

    test "plain let x = ... still works (fast path)" do
      source = """
      mod M
        fn f() -> Int =
          let x = 42
          x
      """

      assert {:ok, _mod, _warnings} = compile(source)
    end

    test "E034 is registered" do
      assert {:ok, text} = Errors.explain("E034")
      assert text =~ "Let Pattern Not Exhaustive"
    end
  end

  # -- Section 1: binary destructuring ---------------------------------------

  describe "binary destructuring" do
    test "binary match with catch-all arm compiles" do
      source = """
      mod M
        fn first_byte(buf: Bitstring) -> Int =
          match buf
            <<b, _rest::binary>> -> b
            <<>> -> 0
      """

      assert {:ok, _mod, _warnings} = compile(source)
    end

    test "binary pattern in let binds segment vars" do
      source = """
      mod M
        fn parse_head(buf: Bitstring) -> Int =
          let <<a, _rest::binary>> = buf
          a
      """

      assert {:ok, _mod, _warnings} = compile(source)
    end

    test "binary pattern in multi-clause fn head compiles" do
      source = """
      mod M
        fn parse(buf: Bitstring) -> Int
          | <<a, _rest::binary>> -> a
          | <<>> -> 0
      """

      assert {:ok, _mod, _warnings} = compile(source)
    end

    test "E031 is registered" do
      assert {:ok, text} = Errors.explain("E031")
      assert text =~ "Binary Pattern Not Exhaustive"
    end
  end

  # -- Section 6: binary exhaustiveness ---------------------------------------

  describe "binary exhaustiveness classifier" do
    test "wildcard alone is exhaustive on Bitstring" do
      patterns = [{:variable, [], "buf"}]
      assert PatternChecker.check_binary_exhaustiveness(:bitstring, patterns) == :exhaustive
    end

    test "open-tail + empty is exhaustive on Bitstring" do
      tail_pat =
        {:literal, [subtype: :bytes],
         [
           {:bin_segment, [], [{:variable, [], "b"}]},
           {:bin_segment, [type: :binary], [{:variable, [], "_rest"}]}
         ]}

      empty_pat = {:literal, [subtype: :bytes], []}

      assert PatternChecker.check_binary_exhaustiveness(:bitstring, [tail_pat, empty_pat]) ==
               :exhaustive
    end

    test "open-tail alone reports <<>> missing" do
      tail_pat =
        {:literal, [subtype: :bytes],
         [
           {:bin_segment, [], [{:variable, [], "b"}]},
           {:bin_segment, [type: :binary], [{:variable, [], "_rest"}]}
         ]}

      assert {:non_exhaustive, witnesses} =
               PatternChecker.check_binary_exhaustiveness(:bitstring, [tail_pat])

      assert match?([_ | _], witnesses)
      assert Enum.any?(witnesses, &(&1 == "<<>>"))
    end

    test "empty alone reports non-empty missing" do
      empty_pat = {:literal, [subtype: :bytes], []}

      assert {:non_exhaustive, witnesses} =
               PatternChecker.check_binary_exhaustiveness(:bitstring, [empty_pat])

      assert match?([_ | _], witnesses)
    end

    test "non-Bitstring scrutinee short-circuits to :exhaustive" do
      patterns = [{:literal, [subtype: :integer], 0}]
      assert PatternChecker.check_binary_exhaustiveness(:int, patterns) == :exhaustive
    end
  end

  # -- Section 8: @derive Functor / Monoid / JSON ----------------------------

  describe "@derive extensions" do
    test "can_derive? recognises the new derivers" do
      assert Derive.can_derive?(:functor)
      assert Derive.can_derive?(:monoid)
      assert Derive.can_derive?(:json)
    end

    test "derive(:functor, ...) emits an fmap/2 function_def" do
      [fn_def] = Derive.derive(:functor, "Box", [:value])
      {:function_def, meta, [_body]} = fn_def
      assert Keyword.get(meta, :name) == "fmap"
      assert Keyword.get(meta, :arity) == 2
    end

    test "derive(:monoid, ...) emits combine/2" do
      [fn_def] = Derive.derive(:monoid, "Bag", [:items])
      {:function_def, meta, [_body]} = fn_def
      assert Keyword.get(meta, :name) == "combine"
      assert Keyword.get(meta, :arity) == 2
    end

    test "derive(:json, ...) emits to_json/1" do
      [fn_def] = Derive.derive(:json, "Point", [:x, :y])
      {:function_def, meta, [_body]} = fn_def
      assert Keyword.get(meta, :name) == "to_json"
      assert Keyword.get(meta, :arity) == 1
    end

    test "derive(:json, ...) on a no-field record emits the literal \"{}\"" do
      [fn_def] = Derive.derive(:json, "Empty", [])
      {:function_def, _meta, [body]} = fn_def
      assert {:literal, [subtype: :string], "{}"} = body
    end

    test "derive(:unknown, ...) returns []" do
      assert [] = Derive.derive(:unknown_typeclass, "Whatever", [:a])
    end
  end

  # -- Section 7: algebra formatter as default -------------------------------

  describe "algebra formatter is the default" do
    test "Cure.Compiler.Formatter.format_algebra/2 round-trips a trivial module" do
      source = "mod M\n  fn f() -> Int = 0\n"

      assert {:ok, formatted} = Cure.Compiler.Formatter.format_algebra(source)
      assert is_binary(formatted)
      # The formatted output must re-parse to a structurally equal AST.
      {:ok, orig_tokens} = Lexer.tokenize(source, emit_events: false)
      {:ok, orig_ast} = Parser.parse(orig_tokens, emit_events: false)
      {:ok, new_tokens} = Lexer.tokenize(formatted, emit_events: false)
      {:ok, new_ast} = Parser.parse(new_tokens, emit_events: false)

      assert strip_lines(orig_ast) == strip_lines(new_ast)
    end
  end

  # -- Helpers ----------------------------------------------------------------

  defp compile(source) do
    Compiler.compile_string(source,
      file: "v0_21_0_test.cure",
      emit_events: false,
      output_dir: @out_dir
    )
  end

  defp tokenize_parse(source) do
    with {:ok, tokens} <- Lexer.tokenize(source, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, emit_events: false) do
      {:ok, ast}
    end
  end

  # Remove line/col metadata from an AST so two parses compare equal
  # modulo position information.
  defp strip_lines({tag, meta, children}) when is_list(meta) do
    meta =
      meta
      |> Keyword.delete(:line)
      |> Keyword.delete(:col)

    {tag, meta, strip_lines(children)}
  end

  defp strip_lines(list) when is_list(list), do: Enum.map(list, &strip_lines/1)
  defp strip_lines(other), do: other
end
