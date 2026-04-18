defmodule Cure.Compiler.RecordDefaultsTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler

  defp compile_and_load(source) do
    Compiler.compile_and_load(source, emit_events: false)
  end

  describe "record fields with default values" do
    test "defaults fill in omitted fields at construction time" do
      source = """
      mod RecordDefaults.Simple
        rec Person
          name: String = "Anonymous"
          age: Int = 0

        fn blank() -> Person = Person{}
        fn named(n: String) -> Person = Person{name: n}
      """

      {:ok, mod} = compile_and_load(source)

      blank = mod.blank()
      assert is_map(blank)
      assert Map.get(blank, :__struct__) == :person
      assert Map.get(blank, :name) == "Anonymous"
      assert Map.get(blank, :age) == 0

      alice = mod.named("Alice")
      assert Map.get(alice, :name) == "Alice"
      # default for age still applies
      assert Map.get(alice, :age) == 0
    end

    test "caller-provided value overrides the default" do
      source = """
      mod RecordDefaults.Override
        rec Counter
          value: Int = 0

        fn custom(v: Int) -> Counter = Counter{value: v}
      """

      {:ok, mod} = compile_and_load(source)
      assert Map.get(mod.custom(42), :value) == 42
    end

    test "records without defaults still work" do
      source = """
      mod RecordDefaults.NoDefaults
        rec Point
          x: Int
          y: Int

        fn origin() -> Point = Point{x: 0, y: 0}
      """

      {:ok, mod} = compile_and_load(source)
      o = mod.origin()
      assert Map.get(o, :x) == 0
      assert Map.get(o, :y) == 0
    end
  end
end
