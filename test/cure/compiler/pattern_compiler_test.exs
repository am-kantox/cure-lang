defmodule Cure.Compiler.PatternCompilerTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Codegen, PatternCompiler}

  defp fresh_state, do: %Codegen{}

  defp compile(ast) do
    {form, _state} = PatternCompiler.compile(ast, fresh_state())
    form
  end

  defp compile_with_guards(ast) do
    PatternCompiler.compile_with_guards(ast, fresh_state())
  end

  describe "literals" do
    test "integer literal" do
      ast = {:literal, [subtype: :integer], 42}
      assert {:integer, _, 42} = compile(ast)
    end

    test "boolean literal" do
      ast = {:literal, [subtype: :boolean], true}
      assert {:atom, _, true} = compile(ast)
    end

    test "symbol literal" do
      ast = {:literal, [subtype: :symbol], :ok}
      assert {:atom, _, :ok} = compile(ast)
    end

    test "negative integer pattern" do
      ast =
        {:unary_op, [operator: :-, line: 1], [{:literal, [subtype: :integer], 5}]}

      assert {:integer, _, -5} = compile(ast)
    end
  end

  describe "variables" do
    test "wildcard _" do
      ast = {:variable, [], "_"}
      assert {:var, _, :_} = compile(ast)
    end

    test "named variable binds into scope" do
      ast = {:variable, [], "x"}
      {form, state} = PatternCompiler.compile(ast, fresh_state())
      assert {:var, _, :V_x} = form
      assert Map.has_key?(state.vars, "x")
    end

    test "underscore-prefixed variable preserves shape" do
      ast = {:variable, [], "_unused"}
      assert {:var, _, :_V_unused} = compile(ast)
    end

    test "repeated occurrence emits equality guard" do
      # Pattern: %[x, x]
      ast =
        {:tuple, [line: 1], [{:variable, [], "x"}, {:variable, [], "x"}]}

      {form, guards, _state} = compile_with_guards(ast)
      assert {:tuple, _, [{:var, _, :V_x}, {:var, _, fresh}]} = form
      assert is_atom(fresh)
      assert [{:op, _, :"=:=", {:var, _, ^fresh}, {:var, _, :V_x}}] = guards
    end
  end

  describe "tuple patterns" do
    test "flat tuple of literals" do
      ast =
        {:tuple, [line: 1], [{:literal, [subtype: :integer], 1}, {:literal, [subtype: :integer], 2}]}

      assert {:tuple, _, [{:integer, _, 1}, {:integer, _, 2}]} = compile(ast)
    end

    test "nested tuple binds inner variable" do
      # %[_, %[a, b]]
      ast =
        {:tuple, [line: 1],
         [
           {:variable, [], "_"},
           {:tuple, [line: 1], [{:variable, [], "a"}, {:variable, [], "b"}]}
         ]}

      form = compile(ast)

      assert {:tuple, _,
              [
                {:var, _, :_},
                {:tuple, _, [{:var, _, :V_a}, {:var, _, :V_b}]}
              ]} = form
    end
  end

  describe "list and cons patterns" do
    test "empty list" do
      assert {nil, _} = compile({:list, [], []})
    end

    test "fixed list of literals" do
      ast =
        {:list, [], [{:literal, [subtype: :integer], 1}, {:literal, [subtype: :integer], 2}]}

      assert {:cons, _, {:integer, _, 1}, {:cons, _, {:integer, _, 2}, {nil, _}}} =
               compile(ast)
    end

    test "cons [h | t] binds both head and tail" do
      ast =
        {:list, [cons: true], [{:variable, [], "h"}, {:variable, [], "t"}]}

      assert {:cons, _, {:var, _, :V_h}, {:var, _, :V_t}} = compile(ast)
    end

    test "nested cons with constructor inside" do
      # [Ok(x) | rest]
      ast =
        {:list, [cons: true],
         [
           {:function_call, [name: "Ok"], [{:variable, [], "x"}]},
           {:variable, [], "rest"}
         ]}

      assert {:cons, _, {:tuple, _, [{:atom, _, :ok}, {:var, _, :V_x}]}, {:var, _, :V_rest}} = compile(ast)
    end
  end

  describe "map patterns" do
    test "map pattern uses map_field_exact, not map_field_assoc" do
      # %{name: n}
      ast =
        {:map, [],
         [
           {:pair, [], [{:literal, [subtype: :symbol], :name}, {:variable, [], "n"}]}
         ]}

      assert {:map, _, [{:map_field_exact, _, {:atom, _, :name}, {:var, _, :V_n}}]} =
               compile(ast)
    end

    test "nested map pattern with cons inside" do
      # %{list: [h | t]}
      ast =
        {:map, [],
         [
           {:pair, [],
            [
              {:literal, [subtype: :symbol], :list},
              {:list, [cons: true], [{:variable, [], "h"}, {:variable, [], "t"}]}
            ]}
         ]}

      assert {:map, _,
              [
                {:map_field_exact, _, {:atom, _, :list}, {:cons, _, {:var, _, :V_h}, {:var, _, :V_t}}}
              ]} = compile(ast)
    end
  end

  describe "record patterns" do
    test "record pattern lowers to map with __struct__ exact match" do
      # Point{x: a, y: b}
      ast =
        {:function_call, [name: "Point", record: true, line: 1],
         [
           {:pair, [], [{:literal, [subtype: :symbol], :x}, {:variable, [], "a"}]},
           {:pair, [], [{:literal, [subtype: :symbol], :y}, {:variable, [], "b"}]}
         ]}

      assert {:map, _,
              [
                {:map_field_exact, _, {:atom, _, :__struct__}, {:atom, _, :point}},
                {:map_field_exact, _, {:atom, _, :x}, {:var, _, :V_a}},
                {:map_field_exact, _, {:atom, _, :y}, {:var, _, :V_b}}
              ]} = compile(ast)
    end

    test "record pattern field punning" do
      # Point{x, y}  -- shorthand for x: x, y: y
      ast =
        {:function_call, [name: "Point", record: true, line: 1], [{:variable, [], "x"}, {:variable, [], "y"}]}

      assert {:map, _,
              [
                {:map_field_exact, _, {:atom, _, :__struct__}, {:atom, _, :point}},
                {:map_field_exact, _, {:atom, _, :x}, {:var, _, :V_x}},
                {:map_field_exact, _, {:atom, _, :y}, {:var, _, :V_y}}
              ]} = compile(ast)
    end
  end

  describe "the full headline example" do
    test "%[_, %{list: [elem_head | elem_tail]}, _] compiles to a proper nested pattern" do
      # Exact shape from the v0.18.0 plan.
      ast =
        {:tuple, [line: 1],
         [
           {:variable, [], "_"},
           {:map, [],
            [
              {:pair, [],
               [
                 {:literal, [subtype: :symbol], :list},
                 {:list, [cons: true], [{:variable, [], "elem_head"}, {:variable, [], "elem_tail"}]}
               ]}
            ]},
           {:variable, [], "_"}
         ]}

      form = compile(ast)

      assert {:tuple, _,
              [
                {:var, _, :_},
                {:map, _,
                 [
                   {:map_field_exact, _, {:atom, _, :list},
                    {:cons, _, {:var, _, :V_elem_head}, {:var, _, :V_elem_tail}}}
                 ]},
                {:var, _, :_}
              ]} = form
    end
  end

  describe "ADT constructor patterns (nested)" do
    test "Ok(Some(x)) compiles to nested tagged tuples, binding x" do
      ast =
        {:function_call, [name: "Ok", line: 1], [{:function_call, [name: "Some", line: 1], [{:variable, [], "x"}]}]}

      assert {:tuple, _,
              [
                {:atom, _, :ok},
                {:tuple, _, [{:atom, _, :some}, {:var, _, :V_x}]}
              ]} = compile(ast)
    end
  end

  describe "pin operator" do
    test "pin with previously-bound variable emits equality guard" do
      # Simulate that "target" is already in scope (e.g., set by an outer `let`).
      state = %Codegen{vars: %{"target" => :V_target}}

      ast = {:pin, [line: 2], [{:variable, [], "target"}]}

      {form, state} = PatternCompiler.compile(ast, state)
      assert {:var, _, fresh_atom} = form
      # The fresh atom is distinct from the existing one.
      refute fresh_atom == :V_target
      # And a guard was accumulated.
      assert [{:op, _, :"=:=", {:var, _, ^fresh_atom}, {:var, _, :V_target}} | _] =
               state.pattern_guards
    end

    test "pin with unknown variable falls back to a fresh binding" do
      ast = {:pin, [line: 2], [{:variable, [], "unknown"}]}
      {form, _state} = PatternCompiler.compile(ast, fresh_state())
      assert {:var, _, :V_unknown} = form
    end
  end
end
