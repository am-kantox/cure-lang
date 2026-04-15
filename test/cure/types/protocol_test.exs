defmodule Cure.Types.ProtocolTest do
  use ExUnit.Case, async: false

  defp compile(source) do
    case Cure.Compiler.compile_and_load(source) do
      {:ok, module} -> module
      {:error, reason} -> flunk("Compilation failed: #{inspect(reason)}")
    end
  end

  defp purge(module) do
    :code.purge(module)
    :code.delete(module)
  end

  setup_all do
    # Load Std.String for use in impls
    Cure.Compiler.compile_and_load(
      File.read!("lib/std/string.cure"),
      file: "lib/std/string.cure"
    )

    :ok
  end

  describe "basic protocol dispatch" do
    test "dispatches on Int and Bool" do
      m =
        compile("""
        mod ShowTest
          proto Show(T)
            fn show(x: T) -> String

          impl Show for Int
            fn show(x: Int) -> String = Std.String.from_int(x)

          impl Show for Bool
            fn show(x: Bool) -> String = if x then "true" else "false"
        """)

      assert m.show(42) == "42"
      assert m.show(-1) == "-1"
      assert m.show(true) == "true"
      assert m.show(false) == "false"
    after
      purge(:"Cure.ShowTest")
    end

    test "dispatches on String and Atom" do
      m =
        compile("""
        mod DescTest
          proto Describe(T)
            fn describe(x: T) -> String

          impl Describe for String
            fn describe(x: String) -> String = "string:" <> x

          impl Describe for Atom
            fn describe(x: Atom) -> String = "atom:" <> Std.String.from_atom(x)
        """)

      assert m.describe("hello") == "string:hello"
      assert m.describe(:world) == "atom:world"
    after
      purge(:"Cure.DescTest")
    end

    test "dispatches on Float" do
      m =
        compile("""
        mod FloatProto
          proto Numeric(T)
            fn double(x: T) -> T

          impl Numeric for Int
            fn double(x: Int) -> Int = x + x

          impl Numeric for Float
            fn double(x: Float) -> Float = x + x
        """)

      assert m.double(21) == 42
      assert m.double(1.5) == 3.0
    after
      purge(:"Cure.FloatProto")
    end

    test "dispatches on List" do
      m =
        compile("""
        mod ListProto
          proto Sizeable(T)
            fn size(x: T) -> Int

          impl Sizeable for List
            fn size(x: List) -> Int = Erlang.Length(x)

          impl Sizeable for String
            fn size(x: String) -> Int = Erlang.Byte_size(x)
        """)

      # List dispatch uses is_list guard
      assert m.size([1, 2, 3]) == 3
      assert m.size("hello") == 5
    after
      purge(:"Cure.ListProto")
    end
  end

  describe "protocol methods used by module functions" do
    test "regular function calls protocol method" do
      m =
        compile("""
        mod CallProto
          proto Show(T)
            fn show(x: T) -> String

          impl Show for Int
            fn show(x: Int) -> String = Std.String.from_int(x)

          fn display_number(n: Int) -> String = "Number: " <> show(n)
        """)

      assert m.display_number(42) == "Number: 42"
    after
      purge(:"Cure.CallProto")
    end

    test "protocol method with multiple params" do
      m =
        compile("""
        mod MultiParam
          proto Format(T)
            fn format(x: T, prefix: String) -> String

          impl Format for Int
            fn format(x: Int, prefix: String) -> String = prefix <> Std.String.from_int(x)

          impl Format for Bool
            fn format(x: Bool, prefix: String) -> String = prefix <> if x then "yes" else "no"
        """)

      assert m.format(42, "val=") == "val=42"
      assert m.format(true, "flag=") == "flag=yes"
    after
      purge(:"Cure.MultiParam")
    end
  end

  describe "multiple protocols in one module" do
    test "two independent protocols" do
      m =
        compile("""
        mod TwoProtos
          proto Show(T)
            fn show(x: T) -> String

          proto Default(T)
            fn default_val(x: T) -> T

          impl Show for Int
            fn show(x: Int) -> String = Std.String.from_int(x)

          impl Default for Int
            fn default_val(x: Int) -> Int = 0

          impl Show for Bool
            fn show(x: Bool) -> String = if x then "true" else "false"

          impl Default for Bool
            fn default_val(x: Bool) -> Bool = false
        """)

      assert m.show(42) == "42"
      assert m.show(true) == "true"
      assert m.default_val(99) == 0
      assert m.default_val(true) == false
    after
      purge(:"Cure.TwoProtos")
    end
  end

  describe "Cure.Types.Protocol module" do
    alias Cure.Types.Protocol

    test "new creates empty context" do
      ctx = Protocol.new()
      assert ctx.protocols == %{}
      assert ctx.implementations == []
    end

    test "mangle_impl_name" do
      assert Protocol.mangle_impl_name("show", "Int") == :show__for__int
      assert Protocol.mangle_impl_name("format", "String") == :format__for__string
    end

    test "type_guard generates correct guards" do
      var = {:var, 1, :V_x}

      assert Protocol.type_guard(var, "Int", 1) == {:call, 1, {:atom, 1, :is_integer}, [var]}
      assert Protocol.type_guard(var, "Float", 1) == {:call, 1, {:atom, 1, :is_float}, [var]}
      assert Protocol.type_guard(var, "String", 1) == {:call, 1, {:atom, 1, :is_binary}, [var]}
      assert Protocol.type_guard(var, "Bool", 1) == {:call, 1, {:atom, 1, :is_boolean}, [var]}
      assert Protocol.type_guard(var, "List", 1) == {:call, 1, {:atom, 1, :is_list}, [var]}
      # User-defined types now get a struct guard instead of nil
      guard = Protocol.type_guard(var, "Person", 1)
      assert guard != nil
      assert {:op, 1, :andalso, {:call, 1, {:atom, 1, :is_map}, [^var]}, _struct_check} = guard
    end

    test "user-defined type guard checks __struct__" do
      var = {:var, 1, :V_x}
      guard = Protocol.type_guard(var, "MyRecord", 1)
      assert {:op, 1, :andalso, _, struct_check} = guard
      assert {:op, 1, :==, _, {:atom, 1, :my_record}} = struct_check
    end
  end
end
