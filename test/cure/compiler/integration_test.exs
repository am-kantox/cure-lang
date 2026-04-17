defmodule Cure.Compiler.IntegrationTest do
  use ExUnit.Case, async: false

  # ============================================================================
  # End-to-end: Cure source -> compile -> load -> call
  # ============================================================================

  describe "end-to-end compilation" do
    test "simple arithmetic function" do
      source = """
      mod BasicMath
        fn add(a: Int, b: Int) -> Int = a + b
      """

      {:ok, module} = Cure.Compiler.compile_and_load(source)
      assert module == :"Cure.BasicMath"
      assert module.add(3, 4) == 7
    after
      purge(:"Cure.BasicMath")
    end

    test "function with multiple expressions in body" do
      source = """
      mod Calc
        fn double(x: Int) -> Int = x * 2
      """

      {:ok, module} = Cure.Compiler.compile_and_load(source)
      assert module.double(21) == 42
    after
      purge(:"Cure.Calc")
    end

    test "module with multiple functions" do
      source = """
      mod Arith
        fn add(a: Int, b: Int) -> Int = a + b
        fn sub(a: Int, b: Int) -> Int = a - b
        fn mul(a: Int, b: Int) -> Int = a * b
      """

      {:ok, module} = Cure.Compiler.compile_and_load(source)
      assert module.add(10, 5) == 15
      assert module.sub(10, 5) == 5
      assert module.mul(10, 5) == 50
    after
      purge(:"Cure.Arith")
    end

    test "@extern FFI to Erlang stdlib" do
      source = """
      mod ExtTest
        @extern(:erlang, :abs, 1)
        fn abs_val(n: Int) -> Int
      """

      {:ok, module} = Cure.Compiler.compile_and_load(source)
      assert module.abs_val(-42) == 42
      assert module.abs_val(42) == 42
    after
      purge(:"Cure.ExtTest")
    end

    test "conditional (if/else)" do
      source = """
      mod Logic
        fn max(a: Int, b: Int) -> Int = if a > b then a else b
      """

      {:ok, module} = Cure.Compiler.compile_and_load(source)
      assert module.max(3, 7) == 7
      assert module.max(10, 2) == 10
    after
      purge(:"Cure.Logic")
    end

    test "pattern matching" do
      source = """
      mod Matcher
        fn describe(x: Int) -> String
          | 0 -> "zero"
          | 1 -> "one"
          | _ -> "other"
      """

      {:ok, module} = Cure.Compiler.compile_and_load(source)
      assert module.describe(0) == "zero"
      assert module.describe(1) == "one"
      assert module.describe(99) == "other"
    after
      purge(:"Cure.Matcher")
    end

    test "let binding" do
      source = """
      mod Binding
        fn compute(x: Int) -> Int = let y = x * 2
      """

      {:ok, module} = Cure.Compiler.compile_and_load(source)
      # let y = x * 2 returns the match result which is x * 2
      assert module.compute(5) == 10
    after
      purge(:"Cure.Binding")
    end

    test "private function is not exported" do
      source = """
      mod Visibility
        fn public_fn() -> Int = 42
        local fn private_fn() -> Int = 99
      """

      {:ok, module} = Cure.Compiler.compile_and_load(source)
      assert module.public_fn() == 42

      # Private function should not be in exports
      exports = module.module_info(:exports)
      refute Enum.any?(exports, fn {name, _} -> name == :private_fn end)
    after
      purge(:"Cure.Visibility")
    end

    test "boolean operations" do
      source = """
      mod BoolTest
        fn both(a: Bool, b: Bool) -> Bool = a and b
        fn either(a: Bool, b: Bool) -> Bool = a or b
      """

      {:ok, module} = Cure.Compiler.compile_and_load(source)
      assert module.both(true, true) == true
      assert module.both(true, false) == false
      assert module.either(false, true) == true
      assert module.either(false, false) == false
    after
      purge(:"Cure.BoolTest")
    end

    test "comparison operations" do
      source = """
      mod CmpTest
        fn is_positive(x: Int) -> Bool = x > 0
      """

      {:ok, module} = Cure.Compiler.compile_and_load(source)
      assert module.is_positive(5) == true
      assert module.is_positive(-3) == false
    after
      purge(:"Cure.CmpTest")
    end

    test "lambda (anonymous function)" do
      source = """
      mod LambdaTest
        fn apply_fn(x: Int) -> Int = let f = fn(n) -> n * 2
      """

      # The declared return type is `Int` but the body is a lambda; this
      # test exercises codegen behaviour, not the type checker, so opt
      # out of the (now default-on) checker.
      {:ok, module} = Cure.Compiler.compile_and_load(source, check_types: false)
      # Returns the lambda itself as match result
      result = module.apply_fn(5)
      assert is_function(result, 1)
      assert result.(5) == 10
    after
      purge(:"Cure.LambdaTest")
    end

    test "record construction and field access" do
      source = """
      mod RecordDemo
        rec Point
          x: Int
          y: Int

        fn make_point(x: Int, y: Int) -> Point = Point{x: x, y: y}
        fn x_coord(p: Point) -> Int = p.x
        fn y_coord(p: Point) -> Int = p.y

        fn translate(p: Point, dx: Int, dy: Int) -> Point =
          Point{x: p.x + dx, y: p.y + dy}

        fn distance_squared(a: Point, b: Point) -> Int =
          let dx = b.x - a.x
          let dy = b.y - a.y
          dx * dx + dy * dy
      """

      {:ok, module} = Cure.Compiler.compile_and_load(source)

      p = module.make_point(3, 4)
      assert module.x_coord(p) == 3
      assert module.y_coord(p) == 4

      q = module.translate(p, 1, 1)
      assert module.x_coord(q) == 4
      assert module.y_coord(q) == 5

      assert module.distance_squared(p, q) == 2
    after
      purge(:"Cure.RecordDemo")
    end

    test "record update syntax TypeName{base | field: val}" do
      source = """
      mod RecordUpdate
        rec Point
          x: Int
          y: Int

        rec Person
          name: String
          age: Int

        fn make_point(x: Int, y: Int) -> Point = Point{x: x, y: y}
        fn make_person(name: String, age: Int) -> Person = Person{name: name, age: age}

        fn set_x(p: Point, new_x: Int) -> Point = Point{p | x: new_x}
        fn set_y(p: Point, new_y: Int) -> Point = Point{p | y: new_y}
        fn move(p: Point, nx: Int, ny: Int) -> Point = Point{p | x: nx, y: ny}
        fn birthday(p: Person) -> Person = Person{p | age: p.age + 1}
        fn rename(p: Person, new_name: String) -> Person = Person{p | name: new_name}
      """

      {:ok, module} = Cure.Compiler.compile_and_load(source)

      p = module.make_point(3, 4)
      # Single-field updates preserve the untouched field
      p2 = module.set_x(p, 10)
      assert p2.x == 10
      assert p2.y == 4

      p3 = module.set_y(p, 99)
      assert p3.x == 3
      assert p3.y == 99

      # Multi-field update
      p4 = module.move(p, 0, 0)
      assert p4.x == 0
      assert p4.y == 0

      person = module.make_person("Alice", 30)
      older = module.birthday(person)
      assert older.age == 31
      assert older.name == "Alice"

      renamed = module.rename(person, "Bob")
      assert renamed.name == "Bob"
      assert renamed.age == 30
    after
      purge(:"Cure.RecordUpdate")
    end
  end

  # Helper to unload a module
  defp purge(module) do
    :code.purge(module)
    :code.delete(module)
  end
end
