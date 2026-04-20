defmodule Cure.Types.TypedPidTest do
  use ExUnit.Case, async: true

  alias Cure.Types.Type
  alias Cure.Compiler.Parser

  describe "Pid type resolution" do
    test "bare `Pid` resolves to the top of the pid lattice" do
      ast = {:variable, [], "Pid"}
      assert Type.resolve(ast) == {:pid, :any}
    end

    test "`Pid(Int)` resolves to `{:pid, :int}`" do
      ast = {:function_call, [name: "Pid"], [{:variable, [], "Int"}]}
      assert Type.resolve(ast) == {:pid, :int}
    end

    test "`Pid(Atom)` resolves to `{:pid, :atom}`" do
      ast = {:function_call, [name: "Pid"], [{:variable, [], "Atom"}]}
      assert Type.resolve(ast) == {:pid, :atom}
    end

    test "unknown inbox name lifts to a `:named` reference" do
      ast = {:function_call, [name: "Pid"], [{:variable, [], "Counter"}]}
      assert Type.resolve(ast) == {:pid, {:named, "Counter"}}
    end
  end

  describe "Ref type resolution" do
    test "`Ref` resolves to the new `:ref` primitive" do
      ast = {:variable, [], "Ref"}
      assert Type.resolve(ast) == :ref
    end
  end

  describe "Pid subtyping" do
    test "covariance in inbox: `Pid(Int)` <: `Pid(Any)`" do
      assert Type.subtype?({:pid, :int}, {:pid, :any})
    end

    test "`Pid(String)` does not subtype `Pid(Int)` -- disjoint primitives" do
      # Covariance still rules out disjoint primitive inboxes. `:any`
      # behaves as both top and bottom in Cure's gradual type system
      # (see the comment on `Type.subtype?/2`), so we use two concrete
      # types to test that the variance is actually enforced.
      refute Type.subtype?({:pid, :string}, {:pid, :int})
    end

    test "reflexivity: `Pid(Int)` <: `Pid(Int)`" do
      assert Type.subtype?({:pid, :int}, {:pid, :int})
    end

    test "legacy bridge: `{:pid, _}` and `:atom` are bidirectionally compatible" do
      # The pre-typed-pid world declared `Pid` as an atom alias; the new
      # typed version keeps interoperating with those signatures.
      assert Type.subtype?({:pid, :int}, :atom)
      assert Type.subtype?(:atom, {:pid, :int})
    end
  end

  describe "Pid display" do
    test "`{:pid, :any}` prints as `Pid`" do
      assert Type.display({:pid, :any}) == "Pid"
    end

    test "`{:pid, :int}` prints as `Pid(Int)`" do
      assert Type.display({:pid, :int}) == "Pid(Int)"
    end

    test "`:ref` prints as `Ref`" do
      assert Type.display(:ref) == "Ref"
    end
  end

  describe "typed send checking" do
    test "a message that matches the inbox type-checks silently" do
      # Parse a function that sends an Int to a Pid(Int).
      src = """
      mod Cure.Test.TypedSendOk
        fn deliver(pid: Pid(Int), n: Int) -> Int = pid <-| n
      """

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
      {:ok, ast} = Parser.parse(tokens, emit_events: false)
      assert {:ok, _} = Cure.Types.Checker.check_module(ast, emit_events: false)
    end

    test "a message of a different type surfaces E046 Inbox Mismatch" do
      src = """
      mod Cure.Test.TypedSendMismatch
        fn deliver(pid: Pid(Int), s: String) -> Int = pid <-| s
      """

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
      {:ok, ast} = Parser.parse(tokens, emit_events: false)

      assert {:error, errors} = Cure.Types.Checker.check_module(ast, emit_events: false)

      assert Enum.any?(errors, fn
               {:inbox_mismatch, msg, _} -> String.contains?(msg, "E046")
               _ -> false
             end)
    end

    test "bare `Pid` parameter still type-checks any message (legacy semantics)" do
      src = """
      mod Cure.Test.TypedSendBarePid
        fn deliver(pid: Pid, msg: Atom) -> Atom = pid <-| msg
      """

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(src, emit_events: false)
      {:ok, ast} = Parser.parse(tokens, emit_events: false)
      assert {:ok, _} = Cure.Types.Checker.check_module(ast, emit_events: false)
    end
  end
end
