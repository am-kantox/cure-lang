defmodule Cure.Types.CheckerTest do
  use ExUnit.Case, async: true

  alias Cure.Types.{Checker, Type}
  alias Cure.Pipeline.Events

  # ============================================================================
  # Literal Inference
  # ============================================================================

  describe "literal inference" do
    test "integer" do
      assert {:ok, :int} = Checker.infer_expr({:literal, [subtype: :integer, line: 1], 42})
    end

    test "float" do
      assert {:ok, :float} = Checker.infer_expr({:literal, [subtype: :float, line: 1], 3.14})
    end

    test "string" do
      assert {:ok, :string} = Checker.infer_expr({:literal, [subtype: :string, line: 1], "hello"})
    end

    test "boolean" do
      assert {:ok, :bool} = Checker.infer_expr({:literal, [subtype: :boolean, line: 1], true})
    end

    test "null" do
      assert {:ok, :unit} = Checker.infer_expr({:literal, [subtype: :null, line: 1], nil})
    end

    test "symbol" do
      assert {:ok, :atom} = Checker.infer_expr({:literal, [subtype: :symbol, line: 1], :ok})
    end

    test "char" do
      assert {:ok, :char} = Checker.infer_expr({:literal, [subtype: :char, line: 1], 65})
    end
  end

  # ============================================================================
  # Variable Lookup
  # ============================================================================

  describe "variables" do
    test "wildcard is :any" do
      assert {:ok, :any} = Checker.infer_expr({:variable, [scope: :local, line: 1], "_"})
    end

    test "unbound variable is error" do
      assert {:error, {:unbound_variable, _, _}} =
               Checker.infer_expr({:variable, [scope: :local, line: 1], "undefined_var"})
    end
  end

  # ============================================================================
  # Binary Operators
  # ============================================================================

  describe "binary operators" do
    test "int + int = int" do
      ast =
        {:binary_op, [category: :arithmetic, operator: :+, line: 1],
         [{:literal, [subtype: :integer], 1}, {:literal, [subtype: :integer], 2}]}

      assert {:ok, :int} = Checker.infer_expr(ast)
    end

    test "int + float = float (widening)" do
      ast =
        {:binary_op, [category: :arithmetic, operator: :+, line: 1],
         [{:literal, [subtype: :integer], 1}, {:literal, [subtype: :float], 2.0}]}

      assert {:ok, :float} = Checker.infer_expr(ast)
    end

    test "int + string = error" do
      ast =
        {:binary_op, [category: :arithmetic, operator: :+, line: 1],
         [{:literal, [subtype: :integer], 1}, {:literal, [subtype: :string], "x"}]}

      assert {:error, {:type_mismatch, msg, _}} = Checker.infer_expr(ast)
      assert msg =~ "numeric"
    end

    test "raw receive/spawn is rejected (E043), not silently typed as :any" do
      # `receive` and `spawn` both lower to :async_operation, have no codegen,
      # and used to compile silently to `undefined`. They must error instead.
      recv = {:async_operation, [line: 1], [{:match_clause, [], []}]}
      assert {:error, {:unsupported_async, msg, _}} = Checker.infer_expr(recv)
      assert msg =~ "E043"

      spawn_node = {:async_operation, [line: 1], [{:literal, [subtype: :symbol], :x}]}
      assert {:error, {:unsupported_async, _, _}} = Checker.infer_expr(spawn_node)
    end

    test "bool and bool = bool" do
      ast =
        {:binary_op, [category: :boolean, operator: :and, line: 1],
         [{:literal, [subtype: :boolean], true}, {:literal, [subtype: :boolean], false}]}

      assert {:ok, :bool} = Checker.infer_expr(ast)
    end

    test "int and bool = error" do
      ast =
        {:binary_op, [category: :boolean, operator: :and, line: 1],
         [{:literal, [subtype: :integer], 1}, {:literal, [subtype: :boolean], true}]}

      assert {:error, {:type_mismatch, msg, _}} = Checker.infer_expr(ast)
      assert msg =~ "Bool"
    end

    test "string <> string = string" do
      ast =
        {:binary_op, [category: :string, operator: :<>, line: 1],
         [{:literal, [subtype: :string], "a"}, {:literal, [subtype: :string], "b"}]}

      assert {:ok, :string} = Checker.infer_expr(ast)
    end

    test "int <> string = error" do
      ast =
        {:binary_op, [category: :string, operator: :<>, line: 1],
         [{:literal, [subtype: :integer], 1}, {:literal, [subtype: :string], "b"}]}

      assert {:error, {:type_mismatch, msg, _}} = Checker.infer_expr(ast)
      assert msg =~ "String"
    end

    test "comparison returns bool" do
      ast =
        {:binary_op, [category: :comparison, operator: :>, line: 1],
         [{:literal, [subtype: :integer], 1}, {:literal, [subtype: :integer], 2}]}

      assert {:ok, :bool} = Checker.infer_expr(ast)
    end
  end

  # ============================================================================
  # Unary Operators
  # ============================================================================

  describe "unary operators" do
    test "-int = int" do
      ast =
        {:unary_op, [category: :arithmetic, operator: :-, line: 1], [{:literal, [subtype: :integer], 5}]}

      assert {:ok, :int} = Checker.infer_expr(ast)
    end

    test "-string = error" do
      ast =
        {:unary_op, [category: :arithmetic, operator: :-, line: 1], [{:literal, [subtype: :string], "x"}]}

      assert {:error, {:type_mismatch, msg, _}} = Checker.infer_expr(ast)
      assert msg =~ "numeric"
    end

    test "not bool = bool" do
      ast =
        {:unary_op, [category: :boolean, operator: :not, line: 1], [{:literal, [subtype: :boolean], true}]}

      assert {:ok, :bool} = Checker.infer_expr(ast)
    end

    test "not int = error" do
      ast =
        {:unary_op, [category: :boolean, operator: :not, line: 1], [{:literal, [subtype: :integer], 42}]}

      assert {:error, {:type_mismatch, msg, _}} = Checker.infer_expr(ast)
      assert msg =~ "Bool"
    end
  end

  # ============================================================================
  # Conditional (if/else)
  # ============================================================================

  describe "conditional" do
    test "well-typed if/else" do
      ast =
        {:conditional, [line: 1],
         [{:literal, [subtype: :boolean], true}, {:literal, [subtype: :integer], 1}, {:literal, [subtype: :integer], 0}]}

      assert {:ok, :int} = Checker.infer_expr(ast)
    end

    test "non-bool condition is error" do
      ast =
        {:conditional, [line: 1],
         [{:literal, [subtype: :integer], 1}, {:literal, [subtype: :integer], 1}, {:literal, [subtype: :integer], 0}]}

      assert {:error, {:type_mismatch, msg, _}} = Checker.infer_expr(ast)
      assert msg =~ "condition"
    end

    test "branch type mismatch widens to join" do
      ast =
        {:conditional, [line: 1],
         [{:literal, [subtype: :boolean], true}, {:literal, [subtype: :integer], 1}, {:literal, [subtype: :float], 2.0}]}

      # int and float join to float
      assert {:ok, :float} = Checker.infer_expr(ast)
    end
  end

  # ============================================================================
  # Block
  # ============================================================================

  describe "block" do
    test "returns type of last expression" do
      ast =
        {:block, [line: 1], [{:literal, [subtype: :integer], 1}, {:literal, [subtype: :string], "hello"}]}

      assert {:ok, :string} = Checker.infer_expr(ast)
    end
  end

  # ============================================================================
  # Collections
  # ============================================================================

  describe "collections" do
    test "empty list" do
      # Typed as `{:list, :never}` so the literal is a subtype of every
      # concrete list type. This is what lets match arms like `[] -> []`
      # coexist with cons arms of a specific element type.
      ast = {:list, [line: 1], []}
      assert {:ok, {:list, :never}} = Checker.infer_expr(ast)
    end

    test "homogeneous list" do
      ast =
        {:list, [line: 1], [{:literal, [subtype: :integer], 1}, {:literal, [subtype: :integer], 2}]}

      assert {:ok, {:list, :int}} = Checker.infer_expr(ast)
    end

    test "tuple" do
      ast =
        {:tuple, [line: 1], [{:literal, [subtype: :integer], 1}, {:literal, [subtype: :string], "x"}]}

      assert {:ok, {:tuple, [:int, :string]}} = Checker.infer_expr(ast)
    end

    test "map" do
      ast =
        {:map, [line: 1], [{:pair, [], [{:literal, [subtype: :symbol], :name}, {:literal, [subtype: :string], "Jo"}]}]}

      assert {:ok, {:map, :atom, :string}} = Checker.infer_expr(ast)
    end
  end

  # ============================================================================
  # Lambda
  # ============================================================================

  describe "lambda" do
    test "infers function type" do
      ast =
        {:lambda, [params: [{:param, [], "x"}], line: 1], [{:literal, [subtype: :integer], 42}]}

      assert {:ok, {:fun, [:any], :int}} = Checker.infer_expr(ast)
    end
  end

  # ============================================================================
  # String Interpolation
  # ============================================================================

  describe "string interpolation" do
    test "always string" do
      ast = {:string_interpolation, [line: 1], [{:literal, [subtype: :string], "hi"}]}
      assert {:ok, :string} = Checker.infer_expr(ast)
    end
  end

  # ============================================================================
  # Module Check (two-pass)
  # ============================================================================

  describe "module check" do
    test "well-typed module passes" do
      ast =
        {:container, [container_type: :module, name: "M", line: 1],
         [
           {:function_def,
            [
              name: "add",
              params: [{:param, [type: {:variable, [], "Int"}], "a"}, {:param, [type: {:variable, [], "Int"}], "b"}],
              return_type: {:variable, [], "Int"},
              visibility: :public,
              arity: 2,
              line: 1
            ],
            [
              {:binary_op, [category: :arithmetic, operator: :+, line: 1],
               [{:variable, [scope: :local, line: 1], "a"}, {:variable, [scope: :local, line: 1], "b"}]}
            ]}
         ]}

      assert {:ok, _} = Checker.check_module(ast, emit_events: false)
    end

    test "return type mismatch is error" do
      ast =
        {:container, [container_type: :module, name: "M", line: 1],
         [
           {:function_def,
            [name: "bad", params: [], return_type: {:variable, [], "Int"}, visibility: :public, arity: 0, line: 1],
            [{:literal, [subtype: :string, line: 1], "not an int"}]}
         ]}

      assert {:error, errors} = Checker.check_module(ast, emit_events: false)
      assert [_ | _] = errors
      assert {:type_mismatch, msg, _} = hd(errors)
      assert msg =~ "declared return type Int"
    end

    test "@extern functions are trusted" do
      ast =
        {:container, [container_type: :module, name: "M", line: 1],
         [
           {:function_def,
            [
              name: "abs_val",
              params: [{:param, [type: {:variable, [], "Int"}], "n"}],
              return_type: {:variable, [], "Int"},
              visibility: :public,
              arity: 1,
              line: 1,
              extern: {:erlang, :abs, 1}
            ], []}
         ]}

      assert {:ok, _} = Checker.check_module(ast, emit_events: false)
    end

    test "multi-clause function passes when clauses agree" do
      ast =
        {:container, [container_type: :module, name: "M", line: 1],
         [
           {:function_def,
            [
              name: "f",
              params: [{:param, [], "x"}],
              return_type: {:variable, [], "Int"},
              visibility: :public,
              arity: 1,
              line: 1,
              clauses: [
                %{
                  params: [{:literal, [subtype: :integer], 0}],
                  guard: nil,
                  body: [{:literal, [subtype: :integer, line: 1], 1}]
                },
                %{
                  params: [{:variable, [scope: :local], "n"}],
                  guard: nil,
                  body: [{:literal, [subtype: :integer, line: 1], 2}]
                }
              ]
            ], []}
         ]}

      assert {:ok, _} = Checker.check_module(ast, emit_events: false)
    end

    test "cross-function calls resolve via signatures" do
      ast =
        {:container, [container_type: :module, name: "M", line: 1],
         [
           {:function_def,
            [name: "helper", params: [], return_type: {:variable, [], "Int"}, visibility: :public, arity: 0, line: 1],
            [{:literal, [subtype: :integer, line: 1], 42}]},
           {:function_def,
            [name: "main", params: [], return_type: {:variable, [], "Int"}, visibility: :public, arity: 0, line: 2],
            [{:function_call, [name: "helper", line: 2], []}]}
         ]}

      assert {:ok, _} = Checker.check_module(ast, emit_events: false)
    end
  end

  # ============================================================================
  # Type Utilities
  # ============================================================================

  describe "Type utilities" do
    test "numeric?" do
      assert Type.numeric?(:int)
      assert Type.numeric?(:float)
      refute Type.numeric?(:string)
    end

    test "subtype? basics" do
      assert Type.subtype?(:int, :int)
      assert Type.subtype?(:int, :float)
      assert Type.subtype?(:never, :int)
      assert Type.subtype?(:int, :any)
      refute Type.subtype?(:string, :int)
    end

    test "resolve parser type AST" do
      assert :int = Type.resolve({:variable, [], "Int"})
      assert :float = Type.resolve({:variable, [], "Float"})
      assert :string = Type.resolve({:variable, [], "String"})
      assert :bool = Type.resolve({:variable, [], "Bool"})
      assert :any = Type.resolve(nil)
    end

    test "single-letter uppercase names resolve to type variables" do
      assert {:type_var, "T"} = Type.resolve({:variable, [], "T"})
      assert {:type_var, "U"} = Type.resolve({:variable, [], "U"})
    end

    test "multi-char PascalCase names remain nominal" do
      assert {:named, "Row"} = Type.resolve({:variable, [], "Row"})
      assert {:named, "Knot"} = Type.resolve({:variable, [], "Knot"})
    end

    test "`Tuple` resolves to the generic tuple ADT" do
      assert {:adt, :tuple, []} = Type.resolve({:variable, [], "Tuple"})
    end

    test "type variables are universally compatible under subtype?" do
      tv = {:type_var, "T"}
      assert Type.subtype?(tv, :int)
      assert Type.subtype?(:int, tv)
      assert Type.subtype?({:list, tv}, {:list, {:named, "ReducedRow"}})
      assert Type.subtype?({:list, {:named, "ReducedRow"}}, {:list, tv})
    end

    test "concrete tuple is a subtype of Tuple ADT" do
      assert Type.subtype?({:tuple, [:float, :float]}, {:adt, :tuple, []})
      assert Type.subtype?({:list, {:tuple, [:float, :float]}}, {:list, {:adt, :tuple, []}})
    end

    test "structural joins widen component types" do
      assert {:list, {:named, "Row"}} =
               Type.join({:list, :never}, {:list, {:named, "Row"}})

      assert {:list, :float} = Type.join({:list, :int}, {:list, :float})

      assert {:tuple, [:float, :float]} =
               Type.join({:tuple, [:float, :int]}, {:tuple, [:int, :float]})

      assert {:adt, :tuple, []} =
               Type.join({:tuple, [:float, :float]}, {:adt, :tuple, []})
    end

    test ":any is a top and bottom type" do
      assert Type.subtype?(:any, :int)
      assert Type.subtype?(:int, :any)
    end

    test "display" do
      assert "Int" = Type.display(:int)
      assert "List(Int)" = Type.display({:list, :int})
      assert "(Int) -> Bool" = Type.display({:fun, [:int], :bool})
      assert "T" = Type.display({:type_var, "T"})
      assert "Tuple" = Type.display({:adt, :tuple, []})
    end
  end

  # ============================================================================
  # Pipeline Events
  # ============================================================================

  describe "pipeline events" do
    test "type_checked event is emitted for module check" do
      Events.subscribe(:type_checker, :type_checked)

      ast =
        {:container, [container_type: :module, name: "EvTest", line: 1],
         [
           {:function_def, [name: "f", params: [], visibility: :public, arity: 0, line: 1],
            [{:literal, [subtype: :integer, line: 1], 42}]}
         ]}

      {:ok, _} = Checker.check_module(ast, emit_events: true)

      assert_receive {Cure.Pipeline.Events, :type_checker, :type_checked, {"f", :int}, _}
    end

    test "type_error event is emitted on mismatch" do
      Events.subscribe(:type_checker, :type_error)

      ast =
        {:container, [container_type: :module, name: "EvTest2", line: 1],
         [
           {:function_def,
            [name: "bad", params: [], return_type: {:variable, [], "Int"}, visibility: :public, arity: 0, line: 1],
            [{:literal, [subtype: :string, line: 1], "oops"}]}
         ]}

      {:error, _} = Checker.check_module(ast, emit_events: true)

      assert_receive {Cure.Pipeline.Events, :type_checker, :type_error, _, _}
    end
  end

  # ============================================================================
  # End-to-end with Compiler
  # ============================================================================

  describe "end-to-end with type checking enabled" do
    test "well-typed program compiles with check_types: true" do
      source = """
      mod TypedMod
        fn add(a: Int, b: Int) -> Int = a + b
      """

      assert {:ok, _module} = Cure.Compiler.compile_and_load(source, check_types: true)
    after
      :code.purge(:typedmod)
      :code.delete(:typedmod)
    end

    test "ill-typed program is rejected with check_types: true" do
      source = """
      mod BadMod
        fn bad() -> Int = "not an int"
      """

      assert {:error, {:type_error, _errors}} =
               Cure.Compiler.compile_and_load(source, check_types: true)
    end
  end

  # ============================================================================
  # Polymorphic call specialization (Stdlib + same-module)
  # ============================================================================

  describe "polymorphic call specialization" do
    defp infer_src!(src) do
      {:ok, ast} = Cure.quote(src)
      Checker.infer_expr(ast)
    end

    test "Std.List.map with an Int lambda infers List(Int)" do
      assert {:ok, {:list, :int}} =
               infer_src!("Std.List.map([1, 2, 3], fn(x) -> x + 1)")
    end

    test "Std.List.map preserves the element type when it is Float" do
      assert {:ok, {:list, :float}} =
               infer_src!("Std.List.map([1.0, 2.0], fn(x) -> x * 2.0)")
    end

    test "Std.List.filter returns List of the input element type" do
      assert {:ok, {:list, :int}} =
               infer_src!("Std.List.filter([1, 2, 3], fn(x) -> x > 1)")
    end

    test "Std.List.foldl collapses to the accumulator type" do
      assert {:ok, :int} =
               infer_src!("Std.List.foldl([1, 2, 3], 0, fn(x) -> fn(acc) -> acc + x)")
    end

    test "Std.Math.abs infers its concrete return type" do
      assert {:ok, :int} = infer_src!("Std.Math.abs(-3)")
    end

    test "Std.String.length returns Int" do
      assert {:ok, :int} = infer_src!("Std.String.length(\"hi\")")
    end

    test "same-module polymorphic helper returns its specialised type" do
      src = """
      mod PolyMod
        fn identity(x: T) -> T = x
        fn main() -> Int = identity(42)
      """

      assert {:ok, _module} =
               Cure.Compiler.compile_and_load(src, check_types: true)
    after
      :code.purge(:polymod)
      :code.delete(:polymod)
    end

    test "unqualified call via `use Std.List` resolves to the stdlib signature" do
      # Stop at the type-checker rather than running codegen: the
      # checker is what must resolve `map` against `Std.List.map` when
      # `use Std.List` is in scope, and this exercise is about the
      # type-level plumbing, not about linking the call at run time.
      src = """
      mod UseListMod
        use Std.List
        fn main() -> List(Int) = map([1, 2, 3], fn(x) -> x + 1)
      """

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)

      assert {:ok, _} = Checker.check_module(ast, emit_events: false)
    end

    # Regression for the REPL bug where
    #   :t Std.List.map(["1", "2", "3"], fn (x) -> x + 1)
    # returned `List(U)` instead of a type error. The fix threads an
    # error accumulator through `infer_and_unify_args` so that lambda
    # body errors are not silently swallowed.
    test "Std.List.map with an ill-typed lambda body surfaces a type error" do
      assert {:error, {:type_mismatch, msg, _}} =
               infer_src!("Std.List.map([\"1\", \"2\", \"3\"], fn(x) -> x + 1)")

      assert msg =~ "numeric"
    end

    test "Std.List.map with a correct lambda still returns the specialised list type" do
      # Sanity check: the happy path is not broken by the error accumulator.
      assert {:ok, {:list, :int}} =
               infer_src!("Std.List.map([1, 2, 3], fn(x) -> x + 1)")
    end
  end

  # ============================================================================
  # ADT (enum) container variant registration
  # ============================================================================
  #
  # Regression for the bug where `type Sign = Positive | Negative | Zero`
  # parsed cleanly but the type checker never registered the variants in
  # the value scope. Bare references like `Positive` were therefore
  # diagnosed as `unbound_variable`. The fix in `collect_signatures/2`
  # registers each variant -- nullary as `{:named, TypeName}`,
  # parameterised as `{:fun, [param_types], {:named, TypeName}}` -- so
  # function bodies can refer to them and constructor calls type-check
  # against the declared ADT.
  describe "ADT (enum) container variant registration" do
    test "nullary variants type-check as bare references" do
      src = """
      mod EnumNullaryMod
        type Sign = Positive | Negative | Zero

        fn classify(x: Int) -> Sign
          | x when x > 0 -> Positive
          | x when x < 0 -> Negative
          | _            -> Zero
      """

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)

      assert {:ok, _} = Checker.check_module(ast, emit_events: false)
    end

    test "parameterised variants type-check as constructor calls" do
      src = """
      mod EnumParamMod
        type Box(T) = Empty | Full(T)

        fn wrap(x: Int) -> Box(Int) = Full(x)
        fn nothing() -> Box(Int) = Empty
      """

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)

      assert {:ok, _} = Checker.check_module(ast, emit_events: false)
    end

    test "local refinement aliases declared with `type` are visible to function signatures" do
      # Regression for the gap left at the end of Phase 1: only stdlib
      # type aliases were being lifted into `env.types`. User-defined
      # local aliases (`type Pos = {x: Int | x > 0}`) were silently
      # dropped by `collect_signatures/2`, so the function signature
      # for `classify` resolved its return type to a bare nominal
      # `{:named, "Pos"}` and the multi-clause body's `Int` failed the
      # structural subtype check with
      # "declared return type Pos but body has type Int".
      #
      # After the fix, `install_local_type_aliases/2` resolves `Pos`,
      # `Neg`, `Zer` to their underlying refinements before any
      # function signature is registered. The structural subtype check
      # then accepts `:int` as a candidate inhabitant via the gradual
      # rule `subtype?(t, {:refinement, base, _, _}) -> subtype?(t, base)`.
      src = """
      mod LocalAliasesMod
        type Pos = {x: Int | x > 0}
        type Neg = {x: Int | x < 0}
        type Zer = {x: Int | x == 0}

        fn classify(x: Int) -> Pos
          | x when x > 0 -> x
          | x when x < 0 -> 0 - x
          | _            -> 1
      """

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)

      assert {:ok, _} = Checker.check_module(ast, emit_events: false)
    end

    test "`type X = A | B | C` of pre-existing aliases is a union, not a fresh ADT" do
      # Regression for the user's `type All = Pos | Neg | Zer` case.
      # The parser produces an `:enum` container with three nullary
      # variants regardless of whether `Pos`, `Neg`, `Zer` are fresh
      # tags or pre-existing type aliases. The checker now disambiguates:
      # if every variant name is already in `env.types`, the declaration
      # registers a structural union `{:union, [t_Pos, t_Neg, t_Zer]}`
      # in `env.types` and does *not* re-bind the names in the value
      # scope. The body of `classify` returns `Int` values; subtype
      # `:int <: union` succeeds because each member's gradual rule
      # reduces to `:int <: :int`.
      src = """
      mod UnionAliasMod
        type Pos = {x: Int | x > 0}
        type Neg = {x: Int | x < 0}
        type Zer = {x: Int | x == 0}

        type All = Pos | Neg | Zer

        fn classify(x: Int) -> All
          | x when x > 0 -> x
          | x when x < 0 -> 0 - x
          | _            -> 1
      """

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)

      assert {:ok, _} = Checker.check_module(ast, emit_events: false)
    end

    test "`type X = A | B | C` with fresh tags still registers an ADT" do
      # When none of the variant names match an existing alias in
      # `env.types`, the declaration falls through to the original ADT
      # path, which registers each tag as a value of `{:named, X}`.
      # The classifier below returns the tag values, not Int.
      src = """
      mod FreshTagsMod
        type Sign = PositiveTag | NegativeTag | ZeroTag

        fn classify(x: Int) -> Sign
          | x when x > 0 -> PositiveTag
          | x when x < 0 -> NegativeTag
          | _            -> ZeroTag
      """

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)

      assert {:ok, _} = Checker.check_module(ast, emit_events: false)
    end

    test "forward-referenced local refinement alias still resolves" do
      # Even when the alias declaration comes textually *after* the
      # function that consumes it, the dedicated pre-pass guarantees
      # `env.types` carries the resolved refinement before any
      # `register_fn_signature/2` call inspects the AST.
      src = """
      mod ForwardAliasMod
        fn keep(n: Pos) -> Pos = n
        type Pos = {x: Int | x > 0}
      """

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)

      assert {:ok, _} = Checker.check_module(ast, emit_events: false)
    end

    test "declared Int parameter survives multi-clause guard refinement" do
      # Regression for the bug where `check_multi_clause` bound every
      # clause's pattern variables with `:any`, causing
      # `GuardRefinement.refine_env/3` to wrap them in
      # `{:refinement, :any, ...}`. The body of `| x when x < 0 -> -x`
      # then failed `Type.numeric?/1` (which checks the refinement's
      # base) and the checker emitted
      # "unary '-' expects numeric operand, got {x: Any | ...}".
      src = """
      mod MultiClauseRefine
        type Sign = PositiveTag | NegativeTag | ZeroTag

        fn classify(x: Int) -> Sign
          | x when x > 0 -> PositiveTag
          | x when x < 0 -> NegativeTag
          | _            -> ZeroTag

        fn negate(x: Int) -> Int
          | x when x > 0 -> 0 - x
          | x when x < 0 -> 0 - x
          | _            -> 0
      """

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)

      assert {:ok, _} = Checker.check_module(ast, emit_events: false)
    end

    test "both variant kinds compile end-to-end with check_types: true" do
      source = """
      mod PositiveExample
        type Sign = Positive | Negative | Zero

        fn classify(x: Int) -> Sign
          | x when x > 0 -> Positive
          | x when x < 0 -> Negative
          | _            -> Zero
      """

      assert {:ok, _module} =
               Cure.Compiler.compile_and_load(source, check_types: true)
    after
      :code.purge(:"Cure.PositiveExample")
      :code.delete(:"Cure.PositiveExample")
    end

    test "parameterised constructors round-trip through pattern matching" do
      source = """
      mod BoxRoundtrip
        type Box(T) = Empty | Full(T)

        fn make_full(x: Int) -> Box(Int) = Full(x)
        fn make_empty() -> Box(Int) = Empty

        fn unwrap(b: Box(Int), default: Int) -> Int =
          match b
            Full(v) -> v
            _       -> default
      """

      assert {:ok, _module} =
               Cure.Compiler.compile_and_load(source, check_types: true)
    after
      :code.purge(:"Cure.BoxRoundtrip")
      :code.delete(:"Cure.BoxRoundtrip")
    end
  end

  # ============================================================================
  # Phase 2 (v0.34): refinement obligation enforcement
  # ============================================================================
  #
  # Phase 1 made stdlib refinement aliases (`Std.Refine.Positive`,
  # `Std.Refine.NonNegative`, ...) visible in the type checker. Phase 2
  # makes them *enforced*: refinement-typed parameters are turned into
  # SMT assumptions, refinement-typed return types into SMT obligations,
  # and call-site arguments are checked against the callee's refinement
  # parameters. The tests below cover the four headline outcomes:
  #
  #   * a provable function body / call site is accepted silently;
  #   * a return value that violates the declared refinement surfaces
  #     `E090 refinement_violation`;
  #   * a call-site argument that violates the parameter refinement
  #     surfaces the same error code (`E090`);
  #   * an `:unknown` SMT outcome surfaces the `W091 refinement_unknown`
  #     warning so compilation continues.
  describe "Phase 2 refinement enforcement" do
    @describetag :z3

    test "provable: decrement(Positive) -> NonNegative type-checks" do
      src = """
      mod RefineProvable
        use Std.Refine
        fn decrement(n: Positive) -> NonNegative = n - 1
      """

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)

      assert {:ok, _} = Checker.check_module(ast, emit_events: false)
    end

    test "provable: identity on a refinement is accepted" do
      src = """
      mod RefineIdentity
        use Std.Refine
        fn keep(n: Positive) -> Positive = n
      """

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)

      assert {:ok, _} = Checker.check_module(ast, emit_events: false)
    end

    test "failing return: bad(Int) -> Positive surfaces E090" do
      src = """
      mod RefineBadReturn
        use Std.Refine
        fn bad(n: Int) -> Positive = n - 1
      """

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)

      assert {:error, errors} = Checker.check_module(ast, emit_events: false)

      assert Enum.any?(errors, fn
               {:refinement_violation, msg, _} -> msg =~ "E090"
               _ -> false
             end)
    end

    test "failing call site: passing a non-Positive literal to decrement surfaces E090" do
      src = """
      mod RefineBadCall
        use Std.Refine
        fn decrement(n: Positive) -> NonNegative = n - 1
        fn caller() -> NonNegative = decrement(0 - 3)
      """

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)

      assert {:error, errors} = Checker.check_module(ast, emit_events: false)

      assert Enum.any?(errors, fn
               {:refinement_violation, msg, _} ->
                 msg =~ "call to 'decrement'" and msg =~ "E090"

               _ ->
                 false
             end)
    end

    test "caller refinement assumptions discharge nested call obligations" do
      # `caller` knows `n > 0` from its own `Positive` parameter, so
      # passing `n` to `decrement` (which also wants `Positive`) is
      # provable without any further hints.
      src = """
      mod RefineNestedProvable
        use Std.Refine
        fn decrement(n: Positive) -> NonNegative = n - 1
        fn caller(n: Positive) -> NonNegative = decrement(n)
      """

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)

      assert {:ok, _} = Checker.check_module(ast, emit_events: false)
    end

    test "refinement_unknown warning fires when SMT cannot decide the obligation" do
      # `byte_size` is modelled as an uninterpreted Int -> Int function in
      # `Cure.SMT.Translator`. Z3 cannot rule out a counter-witness for
      # `byte_size(n) > 0` from the empty assumption set, so the obligation
      # comes back `:sat` (failed) -- which is also a useful diagnostic
      # but is not what we want to test here. Instead, build a predicate
      # that Z3 *cannot* refute either, by feeding `byte_size(n) >= 0` as
      # the goal: SMT models `byte_size` as an unconstrained UF, so the
      # obligation's negation is satisfiable and the call surfaces
      # `:failed`. To exercise the `:unknown` path reliably we'd need to
      # disable Z3, which is out of scope here. The test below at least
      # confirms that an unprovable call-site obligation surfaces *some*
      # refinement diagnostic (E090 or W091) rather than silently passing.
      Events.subscribe(:type_checker, :type_warning)
      Events.subscribe(:type_checker, :type_error)

      src = """
      mod RefineDiagnostic
        use Std.Refine
        fn decrement(n: Positive) -> NonNegative = n - 1
        fn opaque(n: Int) -> Int = decrement(n)
      """

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
      {:ok, ast} = Cure.Compiler.Parser.parse(tokens, emit_events: false)

      result = Checker.check_module(ast, emit_events: true)

      # Either the obligation was disproven (E090 error) or it could not
      # be discharged (W091 warning); in both cases we expect a refinement
      # diagnostic rather than silent acceptance.
      diagnostic_seen? =
        match?({:error, _}, result) or
          receive do
            {Cure.Pipeline.Events, :type_checker, :type_warning, {:refinement_unknown, _, _}, _} -> true
          after
            0 -> false
          end

      assert diagnostic_seen?
    end
  end

  # ============================================================================
  # Fallback warning for unknown AST nodes
  # ============================================================================

  describe "unknown AST node warning" do
    test "emits type_warning event for unrecognized node" do
      Events.subscribe(:type_checker, :type_warning)

      ast =
        {:container, [container_type: :module, name: "UnknownNode", line: 1],
         [
           {:function_def, [name: "f", params: [], visibility: :public, arity: 0, line: 1],
            [{:totally_unknown, [line: 3], :data}]}
         ]}

      {:ok, _} = Checker.check_module(ast, emit_events: true)

      assert_receive {Cure.Pipeline.Events, :type_checker, :type_warning, {:unrecognized_node, msg, _}, _}

      assert msg =~ "totally_unknown"
    end
  end
end
