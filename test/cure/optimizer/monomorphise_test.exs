defmodule Cure.Optimizer.MonomorphiseTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Optimizer.Monomorphise
  alias Cure.Pipeline.Events

  # -- Helpers ----------------------------------------------------------------

  defp parse!(src) do
    {:ok, tokens} = Lexer.tokenize(src, file: "test", emit_events: false)
    {:ok, ast} = Parser.parse(tokens, file: "test", emit_events: false)
    ast
  end

  defp module_body({:container, _, body}), do: body
  defp module_body({:block, _, children}), do: Enum.find_value(children, &module_body_or_nil/1) || []
  defp module_body_or_nil({:container, _, b}), do: b
  defp module_body_or_nil(_), do: nil

  defp function_defs(body), do: Enum.filter(body, &match?({:function_def, _, _}, &1))

  defp fn_name({:function_def, meta, _}), do: Keyword.get(meta, :name)

  defp call_names_in_body({:function_def, _, body}) do
    body
    |> List.flatten()
    |> Enum.flat_map(&extract_call_names/1)
  end

  defp extract_call_names({:function_call, meta, args}) do
    name = Keyword.get(meta, :name, "")
    is_record? = Keyword.get(meta, :record, false)
    nested = Enum.flat_map(args, &extract_call_names/1)
    if is_record?, do: nested, else: [name | nested]
  end

  defp extract_call_names({_tag, _meta, children}) when is_list(children) do
    Enum.flat_map(children, &extract_call_names/1)
  end

  defp extract_call_names(_), do: []

  defp drain_events do
    receive do
      {Events, _stage, kind, payload, _meta} -> [{kind, payload} | drain_events()]
    after
      0 -> []
    end
  end

  # ============================================================================
  # Specialisation policy
  # ============================================================================

  describe "polymorphic detection" do
    test "non-polymorphic module is untouched" do
      ast =
        parse!("""
        mod M
          fn add(a: Int, b: Int) -> Int = a + b
          fn use_it() -> Int = add(1, 2)
        """)

      {new_ast, count} = Monomorphise.run(ast, emit_events: false)

      assert count == 0
      assert new_ast == ast
    end

    test "polymorphic fn with no concrete call sites is not specialised" do
      ast =
        parse!("""
        mod M
          fn id(x: T) -> T = x
        """)

      {new_ast, count} = Monomorphise.run(ast, emit_events: false)

      assert count == 0
      assert new_ast == ast
    end

    test "@extern functions are never specialised" do
      ast =
        parse!("""
        mod M
          @extern(:erlang, :foo, 1)
          fn id(x: T) -> T = x
          fn caller() -> Int = id(42)
        """)

      {_, count} = Monomorphise.run(ast, emit_events: false)
      assert count == 0
    end
  end

  # ============================================================================
  # Specialisation materialisation
  # ============================================================================

  describe "specialisation" do
    test "single Int call site materialises one specialisation" do
      ast =
        parse!("""
        mod M
          fn id(x: T) -> T = x
          fn use_it() -> Int = id(42)
        """)

      {new_ast, count} = Monomorphise.run(ast, emit_events: false)
      defs = new_ast |> module_body() |> function_defs()
      names = Enum.map(defs, &fn_name/1)

      assert count == 1
      # Original `id` and `use_it` are preserved; one specialised clone added.
      assert "id" in names
      assert "use_it" in names
      assert [_clone] = Enum.filter(names, &String.starts_with?(&1, "id__"))
    end

    test "two distinct call types yield two specialisations and both are private" do
      ast =
        parse!("""
        mod M
          fn id(x: T) -> T = x
          fn use_int() -> Int = id(42)
          fn use_str() -> String = id("hi")
        """)

      {new_ast, count} = Monomorphise.run(ast, emit_events: false)
      defs = new_ast |> module_body() |> function_defs()
      clones = Enum.filter(defs, fn d -> d |> fn_name() |> String.starts_with?("id__") end)

      assert count == 2
      assert [_, _] = clones

      Enum.each(clones, fn {:function_def, meta, _} ->
        assert Keyword.get(meta, :visibility) == :private
        assert Keyword.get(meta, :specialised_from) == "id"
      end)
    end

    test "duplicate call substitutions are deduplicated" do
      ast =
        parse!("""
        mod M
          fn id(x: T) -> T = x
          fn a() -> Int = id(1)
          fn b() -> Int = id(2)
          fn c() -> Int = id(3)
        """)

      {new_ast, count} = Monomorphise.run(ast, emit_events: false)
      defs = new_ast |> module_body() |> function_defs()
      clones = Enum.filter(defs, fn d -> d |> fn_name() |> String.starts_with?("id__") end)

      # All three calls share `T = Int` -> only one clone, but every call site
      # is rewritten to it (count == 3).
      assert count == 3
      assert [_one_clone] = clones
    end

    test "original generic is always retained" do
      ast =
        parse!("""
        mod M
          fn id(x: T) -> T = x
          fn use_int() -> Int = id(42)
        """)

      {new_ast, _count} = Monomorphise.run(ast, emit_events: false)
      defs = new_ast |> module_body() |> function_defs()

      assert Enum.any?(defs, fn d -> fn_name(d) == "id" end)
    end
  end

  # ============================================================================
  # Call-site rewriting
  # ============================================================================

  describe "call site rewriting" do
    test "Int call site dispatches to the Int clone" do
      ast =
        parse!("""
        mod M
          fn id(x: T) -> T = x
          fn use_int() -> Int = id(42)
        """)

      {new_ast, _count} = Monomorphise.run(ast, emit_events: false)
      [use_def] = new_ast |> module_body() |> function_defs() |> Enum.filter(&(fn_name(&1) == "use_int"))
      [called] = call_names_in_body(use_def)

      assert String.starts_with?(called, "id__")
      refute called == "id"
    end

    test "different call types get different mangled names" do
      ast =
        parse!("""
        mod M
          fn id(x: T) -> T = x
          fn use_int() -> Int = id(42)
          fn use_str() -> String = id("a")
        """)

      {new_ast, _count} = Monomorphise.run(ast, emit_events: false)
      defs = new_ast |> module_body() |> function_defs()
      [int_called] = defs |> Enum.find(&(fn_name(&1) == "use_int")) |> call_names_in_body()
      [str_called] = defs |> Enum.find(&(fn_name(&1) == "use_str")) |> call_names_in_body()

      assert String.starts_with?(int_called, "id__")
      assert String.starts_with?(str_called, "id__")
      assert int_called != str_called
    end

    test "calls with non-inferrable arg types fall back to generic" do
      # The lightweight oracle skips variable-typed arguments, so this call
      # site is left as-is and the function is never specialised.
      ast =
        parse!("""
        mod M
          fn id(x: T) -> T = x
          fn forward(y: Int) -> Int = id(y)
        """)

      {new_ast, count} = Monomorphise.run(ast, emit_events: false)
      assert count == 0
      assert new_ast == ast
    end
  end

  # ============================================================================
  # Mangled-name stability
  # ============================================================================

  describe "mangled name stability" do
    test "the same substitution produces the same hash on a second run" do
      ast =
        parse!("""
        mod M
          fn id(x: T) -> T = x
          fn use_it() -> Int = id(42)
        """)

      {first, _} = Monomorphise.run(ast, emit_events: false)
      {second, _} = Monomorphise.run(ast, emit_events: false)

      first_clone =
        first
        |> module_body()
        |> function_defs()
        |> Enum.find(fn d -> d |> fn_name() |> String.starts_with?("id__") end)

      second_clone =
        second
        |> module_body()
        |> function_defs()
        |> Enum.find(fn d -> d |> fn_name() |> String.starts_with?("id__") end)

      assert fn_name(first_clone) == fn_name(second_clone)
    end
  end

  # ============================================================================
  # Budget
  # ============================================================================

  describe "budget" do
    test "exceeding the budget emits E064 and a :monomorph_skipped event" do
      ast =
        parse!("""
        mod BudgetTest
          fn id(x: T) -> T = x
          fn a() -> Int = id(1)
          fn b() -> String = id("s")
          fn c() -> Bool = id(true)
        """)

      Events.subscribe(:type_checker, :type_warning)
      Events.subscribe(:type_checker, :monomorph_skipped)
      Events.subscribe(:type_checker, :monomorph_specialised)

      {_, _count} = Monomorphise.run(ast, budget: 2)
      events = drain_events()

      specialised = Enum.filter(events, &match?({:monomorph_specialised, _}, &1))
      skipped = Enum.filter(events, &match?({:monomorph_skipped, _}, &1))
      warnings = Enum.filter(events, &match?({:type_warning, _}, &1))

      assert [_, _] = specialised
      assert [{:monomorph_skipped, {"id", 1, :budget_exhausted, 1}}] = skipped
      assert [{:type_warning, {:monomorph_budget_exceeded, msg, _}}] = warnings
      assert msg =~ "E064"
      assert msg =~ "id/1"
    end

    test "budget below distinct count keeps the original generic intact" do
      ast =
        parse!("""
        mod M
          fn id(x: T) -> T = x
          fn a() -> Int = id(1)
          fn b() -> String = id("s")
          fn c() -> Bool = id(true)
        """)

      {new_ast, _} = Monomorphise.run(ast, budget: 1, emit_events: false)
      defs = new_ast |> module_body() |> function_defs()
      assert Enum.any?(defs, fn d -> fn_name(d) == "id" end)
    end
  end

  # ============================================================================
  # End-to-end via Cure.Compiler.compile_and_load
  # ============================================================================

  describe "end-to-end" do
    test "specialised module compiles, loads, and produces the right values" do
      src = """
      mod CureMonomorphE2E
        fn id(x: T) -> T = x
        fn use_int() -> Int = id(42)
        fn use_str() -> String = id("hello")
      """

      {:ok, mod} =
        Cure.Compiler.compile_and_load(src,
          file: "e2e",
          optimize: true,
          check_types: false,
          monomorphise: true,
          emit_events: false
        )

      assert mod.use_int() == 42
      assert mod.use_str() == "hello"
    end

    test "monomorphisation can be disabled via the opt-out flag" do
      src = """
      mod CureMonomorphOptOut
        fn id(x: T) -> T = x
        fn use_int() -> Int = id(42)
      """

      Events.subscribe(:type_checker, :monomorph_specialised)
      _ = drain_events()

      {:ok, _mod} =
        Cure.Compiler.compile_and_load(src,
          file: "optout",
          optimize: true,
          check_types: false,
          monomorphise: false,
          emit_events: true
        )

      events = drain_events()
      refute Enum.any?(events, &match?({:monomorph_specialised, _}, &1))
    end
  end
end
