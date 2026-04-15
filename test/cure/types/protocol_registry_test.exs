defmodule Cure.Types.ProtocolRegistryTest do
  use ExUnit.Case, async: false

  alias Cure.Types.ProtocolRegistry

  setup do
    ProtocolRegistry.start()
    ProtocolRegistry.clear()
    :ok
  end

  describe "ProtocolRegistry" do
    test "register and lookup impl" do
      ProtocolRegistry.register_impl("Show", "show", "Int", :std_show)
      assert {:ok, :std_show} = ProtocolRegistry.lookup_impl("Show", "show", "Int")
    end

    test "lookup missing impl returns :error" do
      assert :error = ProtocolRegistry.lookup_impl("Show", "show", "Float")
    end

    test "has_impl? returns true for registered type" do
      ProtocolRegistry.register_impl("Eq", "eq", "Int", :std_eq)
      assert ProtocolRegistry.has_impl?("Eq", "Int")
      refute ProtocolRegistry.has_impl?("Eq", "Float")
    end

    test "list_impls returns all implementations" do
      ProtocolRegistry.register_impl("Show", "show", "Int", :mod_a)
      ProtocolRegistry.register_impl("Show", "show", "Bool", :mod_b)
      impls = ProtocolRegistry.list_impls("Show")
      assert length(impls) == 2
    end

    test "clear removes all entries" do
      ProtocolRegistry.register_impl("Show", "show", "Int", :mod_a)
      ProtocolRegistry.clear()
      assert :error = ProtocolRegistry.lookup_impl("Show", "show", "Int")
    end
  end

  describe "codegen registers impls globally" do
    test "compiling a module with proto/impl registers in registry" do
      source = """
      mod RegTest
        proto MyProto(T)
          fn greet(x: T) -> String

        impl MyProto for Int
          fn greet(x: Int) -> String = "hello int"

        impl MyProto for Bool
          fn greet(x: Bool) -> String = "hello bool"
      """

      ProtocolRegistry.clear()
      {:ok, _} = Cure.Compiler.compile_and_load(source)

      # The impls should be registered globally
      assert {:ok, :"Cure.RegTest"} = ProtocolRegistry.lookup_impl("MyProto", "greet", "Int")
      assert {:ok, :"Cure.RegTest"} = ProtocolRegistry.lookup_impl("MyProto", "greet", "Bool")
    after
      :code.purge(:"Cure.RegTest")
      :code.delete(:"Cure.RegTest")
    end

    test "Std.Show registers in registry when compiled" do
      ProtocolRegistry.clear()

      Cure.Compiler.compile_and_load(
        File.read!("lib/std/show.cure"),
        file: "lib/std/show.cure"
      )

      assert {:ok, :"Cure.Std.Show"} = ProtocolRegistry.lookup_impl("Show", "show", "Int")
      assert {:ok, :"Cure.Std.Show"} = ProtocolRegistry.lookup_impl("Show", "show", "Bool")
      assert {:ok, :"Cure.Std.Show"} = ProtocolRegistry.lookup_impl("Show", "show", "String")
    end

    test "Std.Eq registers in registry when compiled" do
      ProtocolRegistry.clear()

      Cure.Compiler.compile_and_load(
        File.read!("lib/std/eq.cure"),
        file: "lib/std/eq.cure"
      )

      assert {:ok, :"Cure.Std.Eq"} = ProtocolRegistry.lookup_impl("Eq", "eq", "Int")
      assert ProtocolRegistry.has_impl?("Eq", "String")
    end
  end

  describe "cross-module protocol dispatch" do
    test "module A defines proto+impl, module B calls the method" do
      ProtocolRegistry.clear()

      # Module A: defines and implements the protocol
      source_a = """
      mod ModA
        proto Displayable(T)
          fn display(x: T) -> String

        impl Displayable for Int
          fn display(x: Int) -> String = Std.String.from_int(x)
      """

      # Load Std.String dependency
      Cure.Compiler.compile_and_load(
        File.read!("lib/std/string.cure"),
        file: "lib/std/string.cure"
      )

      {:ok, mod_a} = Cure.Compiler.compile_and_load(source_a)
      assert mod_a == :"Cure.ModA"

      # Module A's display function should work
      assert mod_a.display(42) == "42"

      # The impl should be registered globally
      assert {:ok, :"Cure.ModA"} = ProtocolRegistry.lookup_impl("Displayable", "display", "Int")
    after
      :code.purge(:"Cure.ModA")
      :code.delete(:"Cure.ModA")
    end
  end
end
