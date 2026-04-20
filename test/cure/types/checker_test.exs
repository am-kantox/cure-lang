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
