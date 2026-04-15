defmodule Cure.Compiler.CodegenTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.Codegen
  alias Cure.Pipeline.Events

  # Helper: compile an expression and return the form
  defp expr(ast) do
    {:ok, form} = Codegen.compile_expr(ast)
    form
  end

  # ============================================================================
  # Literals
  # ============================================================================

  describe "literals" do
    test "integer" do
      assert {:integer, _, 42} = expr({:literal, [subtype: :integer, line: 1, col: 1], 42})
    end

    test "float" do
      assert {:float, _, 3.14} = expr({:literal, [subtype: :float, line: 1, col: 1], 3.14})
    end

    test "string" do
      form = expr({:literal, [subtype: :string, line: 1, col: 1], "hello"})
      assert {:bin, 1, [{:bin_element, 1, {:string, 1, ~c"hello"}, :default, [:utf8]}]} = form
    end

    test "boolean true" do
      assert {:atom, _, true} = expr({:literal, [subtype: :boolean, line: 1, col: 1], true})
    end

    test "boolean false" do
      assert {:atom, _, false} = expr({:literal, [subtype: :boolean, line: 1, col: 1], false})
    end

    test "null" do
      assert {:atom, _, nil} = expr({:literal, [subtype: :null, line: 1, col: 1], nil})
    end

    test "symbol (atom)" do
      assert {:atom, _, :ok} = expr({:literal, [subtype: :symbol, line: 1, col: 1], :ok})
    end

    test "char" do
      assert {:integer, _, 65} = expr({:literal, [subtype: :char, line: 1, col: 1], 65})
    end
  end

  # ============================================================================
  # Variables
  # ============================================================================

  describe "variables" do
    test "simple variable is mangled" do
      form = expr({:variable, [scope: :local, line: 1, col: 1], "x"})
      assert {:var, _, :V_x} = form
    end

    test "underscore wildcard" do
      form = expr({:variable, [scope: :local, line: 1, col: 1], "_"})
      assert {:var, _, :_} = form
    end

    test "snake_case variable" do
      form = expr({:variable, [scope: :local, line: 1, col: 1], "my_var"})
      assert {:var, _, :V_my_var} = form
    end
  end

  # ============================================================================
  # Binary Operators
  # ============================================================================

  describe "binary operators" do
    test "addition" do
      ast =
        {:binary_op, [category: :arithmetic, operator: :+, line: 1, col: 1],
         [{:literal, [subtype: :integer, line: 1, col: 1], 1}, {:literal, [subtype: :integer, line: 1, col: 3], 2}]}

      form = expr(ast)
      assert {:op, 1, :+, {:integer, _, 1}, {:integer, _, 2}} = form
    end

    test "comparison operators map correctly" do
      ast =
        {:binary_op, [category: :comparison, operator: :<=, line: 1, col: 1],
         [{:variable, [scope: :local], "a"}, {:variable, [scope: :local], "b"}]}

      form = expr(ast)
      assert {:op, _, :"=<", _, _} = form
    end

    test "boolean and -> andalso" do
      ast =
        {:binary_op, [category: :boolean, operator: :and, line: 1, col: 1],
         [{:literal, [subtype: :boolean], true}, {:literal, [subtype: :boolean], false}]}

      form = expr(ast)
      assert {:op, _, :andalso, _, _} = form
    end

    test "boolean or -> orelse" do
      ast =
        {:binary_op, [category: :boolean, operator: :or, line: 1, col: 1],
         [{:literal, [subtype: :boolean], true}, {:literal, [subtype: :boolean], false}]}

      form = expr(ast)
      assert {:op, _, :orelse, _, _} = form
    end

    test "string concat <> -> iolist_to_binary" do
      ast =
        {:binary_op, [category: :string, operator: :<>, line: 1, col: 1],
         [
           {:literal, [subtype: :string, line: 1, col: 1], "hello"},
           {:literal, [subtype: :string, line: 1, col: 1], " world"}
         ]}

      form = expr(ast)

      assert {:call, _, {:remote, _, {:atom, _, :erlang}, {:atom, _, :iolist_to_binary}}, [_iolist]} = form
    end

    test "modulo -> rem" do
      ast =
        {:binary_op, [category: :arithmetic, operator: :%, line: 1, col: 1],
         [{:literal, [subtype: :integer], 10}, {:literal, [subtype: :integer], 3}]}

      assert {:op, _, :rem, _, _} = expr(ast)
    end

    test "not equal -> /=" do
      ast =
        {:binary_op, [category: :comparison, operator: :!=, line: 1, col: 1],
         [{:literal, [subtype: :integer], 1}, {:literal, [subtype: :integer], 2}]}

      assert {:op, _, :"/=", _, _} = expr(ast)
    end
  end

  # ============================================================================
  # Unary Operators
  # ============================================================================

  describe "unary operators" do
    test "negation" do
      ast =
        {:unary_op, [category: :arithmetic, operator: :-, line: 1, col: 1],
         [{:literal, [subtype: :integer, line: 1, col: 2], 5}]}

      form = expr(ast)
      assert {:op, _, :-, {:integer, _, 5}} = form
    end

    test "not" do
      ast =
        {:unary_op, [category: :boolean, operator: :not, line: 1, col: 1],
         [{:literal, [subtype: :boolean, line: 1, col: 5], true}]}

      form = expr(ast)
      assert {:op, _, :not, {:atom, _, true}} = form
    end
  end

  # ============================================================================
  # Function Calls
  # ============================================================================

  describe "function calls" do
    test "local call" do
      ast =
        {:function_call, [name: "add", line: 1, col: 1],
         [{:literal, [subtype: :integer], 1}, {:literal, [subtype: :integer], 2}]}

      form = expr(ast)
      assert {:call, _, {:atom, _, :add}, [_, _]} = form
    end

    test "zero-arg call" do
      ast = {:function_call, [name: "get_value", line: 1, col: 1], []}
      form = expr(ast)
      assert {:call, _, {:atom, _, :get_value}, []} = form
    end

    test "qualified call (Mod.fun)" do
      ast =
        {:function_call, [name: "Std.List.reverse", line: 1, col: 1], [{:variable, [scope: :local], "xs"}]}

      form = expr(ast)
      assert {:call, _, {:remote, _, {:atom, _, :"Cure.Std.List"}, {:atom, _, :reverse}}, [_]} = form
    end

    test "ADT constructor call (PascalCase)" do
      ast =
        {:function_call, [name: "Ok", line: 1, col: 1], [{:literal, [subtype: :integer], 42}]}

      form = expr(ast)
      assert {:tuple, _, [{:atom, _, :ok}, {:integer, _, 42}]} = form
    end

    test "nullary ADT constructor" do
      ast = {:function_call, [name: "None", line: 1, col: 1], []}
      form = expr(ast)
      assert {:tuple, _, [{:atom, _, :none}]} = form
    end
  end

  # ============================================================================
  # Let Binding (Assignment)
  # ============================================================================

  describe "let binding" do
    test "simple let x = 42" do
      ast =
        {:assignment, [line: 1, col: 1], [{:variable, [scope: :local], "x"}, {:literal, [subtype: :integer], 42}]}

      form = expr(ast)
      assert {:match, _, {:var, _, :V_x}, {:integer, _, 42}} = form
    end
  end

  # ============================================================================
  # Conditional (if/else)
  # ============================================================================

  describe "conditional" do
    test "if/else compiles to case on boolean" do
      ast =
        {:conditional, [line: 1, col: 1],
         [
           {:literal, [subtype: :boolean, line: 1], true},
           {:literal, [subtype: :integer, line: 1], 1},
           {:literal, [subtype: :integer, line: 1], 0}
         ]}

      form = expr(ast)

      assert {:case, _, {:atom, _, true},
              [
                {:clause, _, [{:atom, _, true}], [], [{:integer, _, 1}]},
                {:clause, _, [{:atom, _, false}], [], [{:integer, _, 0}]}
              ]} = form
    end
  end

  # ============================================================================
  # Pattern Match
  # ============================================================================

  describe "pattern match" do
    test "simple match expression" do
      ast =
        {:pattern_match, [line: 1, col: 1],
         [
           {:variable, [scope: :local], "x"},
           {:match_arm, [pattern: {:literal, [subtype: :integer], 0}],
            [{:literal, [subtype: :string, line: 1], "zero"}]},
           {:match_arm, [pattern: {:variable, [scope: :local], "_"}],
            [{:literal, [subtype: :string, line: 1], "other"}]}
         ]}

      form = expr(ast)
      assert {:case, _, {:var, _, :V_x}, [_, _]} = form
    end
  end

  # ============================================================================
  # Block
  # ============================================================================

  describe "block" do
    test "single expression unwraps" do
      ast =
        {:block, [line: 1, col: 1], [{:literal, [subtype: :integer, line: 1], 42}]}

      form = expr(ast)
      assert {:integer, _, 42} = form
    end

    test "multiple expressions become block" do
      ast =
        {:block, [line: 1, col: 1],
         [{:literal, [subtype: :integer, line: 1], 1}, {:literal, [subtype: :integer, line: 1], 2}]}

      form = expr(ast)
      assert {:block, _, [{:integer, _, 1}, {:integer, _, 2}]} = form
    end
  end

  # ============================================================================
  # Collections
  # ============================================================================

  describe "collections" do
    test "empty list" do
      ast = {:list, [line: 1, col: 1], []}
      form = expr(ast)
      assert {nil, _} = form
    end

    test "list of integers" do
      ast =
        {:list, [line: 1, col: 1],
         [{:literal, [subtype: :integer], 1}, {:literal, [subtype: :integer], 2}, {:literal, [subtype: :integer], 3}]}

      form = expr(ast)
      assert {:cons, _, {:integer, _, 1}, {:cons, _, {:integer, _, 2}, {:cons, _, {:integer, _, 3}, {nil, _}}}} = form
    end

    test "cons list [h | t]" do
      ast =
        {:list, [cons: true, line: 1, col: 1], [{:variable, [scope: :local], "h"}, {:variable, [scope: :local], "t"}]}

      form = expr(ast)
      assert {:cons, _, {:var, _, :V_h}, {:var, _, :V_t}} = form
    end

    test "tuple" do
      ast =
        {:tuple, [line: 1, col: 1], [{:literal, [subtype: :integer], 1}, {:literal, [subtype: :integer], 2}]}

      form = expr(ast)
      assert {:tuple, _, [{:integer, _, 1}, {:integer, _, 2}]} = form
    end

    test "map with atom keys" do
      ast =
        {:map, [line: 1, col: 1],
         [{:pair, [], [{:literal, [subtype: :symbol], :name}, {:literal, [subtype: :string, line: 1], "Jo"}]}]}

      form = expr(ast)
      assert {:map, _, [{:map_field_assoc, _, {:atom, _, :name}, _}]} = form
    end
  end

  # ============================================================================
  # Lambda
  # ============================================================================

  describe "lambda" do
    test "simple lambda fn(x) -> x" do
      ast =
        {:lambda, [params: [{:param, [], "x"}], line: 1, col: 1], [{:variable, [scope: :local, line: 1, col: 1], "x"}]}

      form = expr(ast)
      assert {:fun, _, {:clauses, [{:clause, _, [{:var, _, :V_x}], [], [{:var, _, :V_x}]}]}} = form
    end
  end

  # ============================================================================
  # String Interpolation
  # ============================================================================

  describe "string interpolation" do
    test "interpolation compiles to iolist_to_binary" do
      ast =
        {:string_interpolation, [line: 1, col: 1],
         [{:literal, [subtype: :string], "hello "}, {:variable, [scope: :local, line: 1, col: 1], "name"}]}

      form = expr(ast)

      assert {:call, _, {:remote, _, {:atom, _, :erlang}, {:atom, _, :iolist_to_binary}}, [_iolist]} = form
    end
  end

  # ============================================================================
  # Attribute Access
  # ============================================================================

  describe "attribute access" do
    test "obj.field -> maps:get(field, obj)" do
      ast =
        {:attribute_access, [attribute: "name", line: 1, col: 1], [{:variable, [scope: :local, line: 1], "person"}]}

      form = expr(ast)
      assert {:call, _, {:remote, _, {:atom, _, :maps}, {:atom, _, :get}}, [{:atom, _, :name}, _]} = form
    end
  end

  # ============================================================================
  # Range
  # ============================================================================

  describe "range" do
    test "inclusive range -> lists:seq(a, b)" do
      ast =
        {:range, [inclusive: true, line: 1, col: 1],
         [{:literal, [subtype: :integer], 1}, {:literal, [subtype: :integer], 10}]}

      form = expr(ast)

      assert {:call, _, {:remote, _, {:atom, _, :lists}, {:atom, _, :seq}}, [{:integer, _, 1}, {:integer, _, 10}]} =
               form
    end

    test "exclusive range -> lists:seq(a, b - 1)" do
      ast =
        {:range, [inclusive: false, line: 1, col: 1],
         [{:literal, [subtype: :integer], 1}, {:literal, [subtype: :integer], 10}]}

      form = expr(ast)

      assert {:call, _, {:remote, _, {:atom, _, :lists}, {:atom, _, :seq}},
              [{:integer, _, 1}, {:op, _, :-, {:integer, _, 10}, {:integer, _, 1}}]} = form
    end
  end

  # ============================================================================
  # Early Return & Throw
  # ============================================================================

  describe "early return and throw" do
    test "early return -> throw({:cure_return, val})" do
      ast =
        {:early_return, [line: 1, col: 1], [{:literal, [subtype: :integer], 42}]}

      form = expr(ast)
      assert {:call, _, {:atom, _, :throw}, [{:tuple, _, [{:atom, _, :cure_return}, {:integer, _, 42}]}]} = form
    end

    test "throw -> erlang:throw(val)" do
      ast =
        {:throw, [line: 1, col: 1], [{:literal, [subtype: :string, line: 1], "error"}]}

      form = expr(ast)
      assert {:call, _, {:remote, _, {:atom, _, :erlang}, {:atom, _, :throw}}, [_]} = form
    end
  end

  # ============================================================================
  # Comprehension
  # ============================================================================

  describe "comprehension" do
    test "list comprehension -> lc form" do
      ast =
        {:comprehension, [line: 1, col: 1],
         [
           {:binary_op, [category: :arithmetic, operator: :*, line: 1, col: 1],
            [{:variable, [scope: :local], "x"}, {:literal, [subtype: :integer], 2}]},
           {:generator, [], [{:variable, [scope: :local], "x"}, {:variable, [scope: :local], "xs"}]}
         ]}

      form = expr(ast)
      assert {:lc, _, _, [_generator]} = form
    end
  end

  # ============================================================================
  # Module Assembly
  # ============================================================================

  describe "module assembly" do
    test "simple module with one function" do
      ast =
        {:container, [container_type: :module, name: "Math", language: :cure, line: 1, col: 1],
         [
           {:function_def,
            [
              name: "add",
              params: [{:param, [], "a"}, {:param, [], "b"}],
              visibility: :public,
              arity: 2,
              line: 2,
              col: 3
            ],
            [
              {:binary_op, [category: :arithmetic, operator: :+, line: 2, col: 20],
               [{:variable, [scope: :local], "a"}, {:variable, [scope: :local], "b"}]}
            ]}
         ]}

      {:ok, forms} = Codegen.compile_module(ast, emit_events: false)

      assert [
               {:attribute, _, :module, :"Cure.Math"},
               {:attribute, _, :export, [{:add, 2}]},
               {:function, _, :add, 2, [_clause]}
             ] = forms
    end

    test "module with public and private functions" do
      ast =
        {:container, [container_type: :module, name: "MyMod", line: 1, col: 1],
         [
           {:function_def, [name: "public_fn", params: [], visibility: :public, arity: 0, line: 1],
            [{:literal, [subtype: :integer], 1}]},
           {:function_def, [name: "private_fn", params: [], visibility: :private, arity: 0, line: 2],
            [{:literal, [subtype: :integer], 2}]}
         ]}

      {:ok, forms} = Codegen.compile_module(ast, emit_events: false)

      # Only public_fn in exports
      {:attribute, _, :export, exports} = Enum.at(forms, 1)
      assert {:public_fn, 0} in exports
      refute Enum.any?(exports, fn {name, _} -> name == :private_fn end)

      # Both functions should have forms
      fn_forms =
        Enum.filter(forms, fn
          {:function, _, _, _, _} -> true
          _ -> false
        end)

      assert [_, _] = fn_forms
    end

    test "@extern function generates wrapper" do
      ast =
        {:container, [container_type: :module, name: "Io", line: 1, col: 1],
         [
           {:function_def,
            [
              name: "format",
              params: [{:param, [], "s"}],
              visibility: :public,
              arity: 1,
              line: 1,
              col: 1,
              extern: {:io, :format, 1}
            ], []}
         ]}

      {:ok, forms} = Codegen.compile_module(ast, emit_events: false)

      fn_form =
        Enum.find(forms, fn
          {:function, _, _, _, _} -> true
          _ -> false
        end)

      {:function, _, :format, 1, [{:clause, _, _, _, [body]}]} = fn_form
      assert {:call, _, {:remote, _, {:atom, _, :io}, {:atom, _, :format}}, [_]} = body
    end

    test "multi-clause function" do
      ast =
        {:container, [container_type: :module, name: "Math", line: 1, col: 1],
         [
           {:function_def,
            [
              name: "factorial",
              params: [{:param, [], "n"}],
              visibility: :public,
              arity: 1,
              line: 1,
              clauses: [
                %{params: [{:literal, [subtype: :integer], 0}], guard: nil, body: [{:literal, [subtype: :integer], 1}]},
                %{
                  params: [{:variable, [scope: :local], "n"}],
                  guard: nil,
                  body: [
                    {:binary_op, [category: :arithmetic, operator: :*, line: 1, col: 1],
                     [
                       {:variable, [scope: :local], "n"},
                       {:function_call, [name: "factorial", line: 1, col: 1],
                        [
                          {:binary_op, [category: :arithmetic, operator: :-, line: 1, col: 1],
                           [{:variable, [scope: :local], "n"}, {:literal, [subtype: :integer], 1}]}
                        ]}
                     ]}
                  ]
                }
              ]
            ], []}
         ]}

      {:ok, forms} = Codegen.compile_module(ast, emit_events: false)

      fn_form =
        Enum.find(forms, fn
          {:function, _, _, _, _} -> true
          _ -> false
        end)

      {:function, _, :factorial, 1, clauses} = fn_form
      assert [_, _] = clauses
    end
  end

  # ============================================================================
  # Record Construction and Field Access
  # ============================================================================

  describe "record construction" do
    test "Name{field: val} compiles to a map with __struct__ tag" do
      ast =
        {:function_call, [name: "Point", record: true, line: 1, col: 1],
         [
           {:pair, [], [{:literal, [subtype: :symbol], :x}, {:literal, [subtype: :integer], 3}]},
           {:pair, [], [{:literal, [subtype: :symbol], :y}, {:literal, [subtype: :integer], 4}]}
         ]}

      form = expr(ast)

      assert {:map, _,
              [
                {:map_field_assoc, _, {:atom, _, :__struct__}, {:atom, _, :point}},
                {:map_field_assoc, _, {:atom, _, :x}, {:integer, _, 3}},
                {:map_field_assoc, _, {:atom, _, :y}, {:integer, _, 4}}
              ]} = form
    end

    test "field values are compiled correctly" do
      ast =
        {:function_call, [name: "Box", record: true, line: 1, col: 1],
         [
           {:pair, [],
            [
              {:literal, [subtype: :symbol], :width},
              {:binary_op, [operator: :+, line: 1, col: 1],
               [{:literal, [subtype: :integer], 2}, {:literal, [subtype: :integer], 3}]}
            ]}
         ]}

      form = expr(ast)

      assert {:map, _,
              [
                {:map_field_assoc, _, {:atom, _, :__struct__}, {:atom, _, :box}},
                {:map_field_assoc, _, {:atom, _, :width}, {:op, _, :+, _, _}}
              ]} = form
    end

    test "empty record compiles to a map with only __struct__" do
      ast = {:function_call, [name: "Empty", record: true, line: 1, col: 1], []}
      form = expr(ast)
      assert {:map, _, [{:map_field_assoc, _, {:atom, _, :__struct__}, {:atom, _, :empty}}]} = form
    end
  end

  describe "record field access" do
    test "record.field compiles to maps:get(field, record)" do
      ast =
        {:attribute_access, [attribute: "x", line: 1, col: 1], [{:variable, [scope: :local, line: 1], "p"}]}

      form = expr(ast)

      assert {:call, _, {:remote, _, {:atom, _, :maps}, {:atom, _, :get}}, [{:atom, _, :x}, {:var, _, :V_p}]} = form
    end
  end

  # ============================================================================
  # Name Mangling
  # ============================================================================

  describe "name mangling" do
    test "variable mangling" do
      assert Codegen.mangle_var("x") == :V_x
      assert Codegen.mangle_var("_") == :_
      assert Codegen.mangle_var("_unused") == :V__unused
    end

    test "function name mangling" do
      assert Codegen.mangle_fn_name("add") == :add
      assert Codegen.mangle_fn_name("myFunc") == :myfunc
    end

    test "module name to atom" do
      assert Codegen.cure_module_to_atom("Std.Core") == :"Cure.Std.Core"
      assert Codegen.cure_module_to_atom("MyApp.Users") == :"Cure.MyApp.Users"
    end
  end

  # ============================================================================
  # Pipeline Events
  # ============================================================================

  describe "pipeline events" do
    test "module_assembled event is emitted" do
      Events.subscribe(:codegen, :module_assembled)

      ast =
        {:container, [container_type: :module, name: "EventTest", line: 1, col: 1],
         [
           {:function_def, [name: "hello", params: [], visibility: :public, arity: 0, line: 1],
            [{:literal, [subtype: :integer], 42}]}
         ]}

      {:ok, _forms} = Codegen.compile_module(ast, emit_events: true)

      assert_receive {Cure.Pipeline.Events, :codegen, :module_assembled, _forms, _meta}
    end

    test "form_generated event is emitted for each function" do
      Events.subscribe(:codegen, :form_generated)

      ast =
        {:container, [container_type: :module, name: "EventTest2", line: 1, col: 1],
         [
           {:function_def, [name: "f1", params: [], visibility: :public, arity: 0, line: 1],
            [{:literal, [subtype: :integer], 1}]},
           {:function_def, [name: "f2", params: [], visibility: :public, arity: 0, line: 2],
            [{:literal, [subtype: :integer], 2}]}
         ]}

      {:ok, _forms} = Codegen.compile_module(ast, emit_events: true)

      assert_receive {Cure.Pipeline.Events, :codegen, :form_generated, _, _}
      assert_receive {Cure.Pipeline.Events, :codegen, :form_generated, _, _}
    end

    test "warning event emitted for unrecognized AST node" do
      Events.subscribe(:codegen, :warning)

      ast =
        {:container, [container_type: :module, name: "WarnTest", line: 1, col: 1],
         [
           {:function_def, [name: "f", params: [], visibility: :public, arity: 0, line: 1],
            [{:unknown_node, [line: 5], :something}]}
         ]}

      {:ok, _forms} = Codegen.compile_module(ast, emit_events: true)

      assert_receive {Cure.Pipeline.Events, :codegen, :warning, {:unrecognized_node, msg, _}, _}

      assert msg =~ "unknown_node"
    end
  end

  # ============================================================================
  # String Interpolation (wrap_to_iodata)
  # ============================================================================

  describe "string interpolation with non-string values" do
    test "integer interpolation compiles and runs" do
      source = """
      mod InterpInt
        fn msg() -> String = "value is #{42}"
      """

      {:ok, mod} = Cure.Compiler.compile_and_load(source)
      assert mod.msg() == "value is 42"
    after
      :code.purge(:"Cure.InterpInt")
      :code.delete(:"Cure.InterpInt")
    end

    test "atom interpolation compiles and runs" do
      source = """
      mod InterpAtom
        fn msg() -> String = "status: #{:ok}"
      """

      {:ok, mod} = Cure.Compiler.compile_and_load(source)
      assert mod.msg() == "status: ok"
    after
      :code.purge(:"Cure.InterpAtom")
      :code.delete(:"Cure.InterpAtom")
    end
  end

  # ============================================================================
  # Bytes Literal
  # ============================================================================

  describe "bytes literal" do
    test "binary bytes compile to bin form" do
      form = expr({:literal, [subtype: :bytes, line: 1], <<1, 2, 3>>})
      assert {:bin, 1, [{:bin_element, 1, {:string, 1, [1, 2, 3]}, :default, :default}]} = form
    end

    test "list bytes compile to bin form with elements" do
      form = expr({:literal, [subtype: :bytes, line: 1], [65, 66, 67]})
      assert {:bin, 1, elements} = form
      assert [_, _, _] = elements
    end
  end
end
