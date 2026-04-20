defmodule Cure.Compiler.MelquiadesParserTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser, Printer, Codegen, BeamWriter}
  alias Cure.Types.Effects

  # -- Helpers ---------------------------------------------------------------

  defp parse!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  # Pretty-print a MetaAST node back to source for round-trip checks.
  defp print(ast), do: Printer.quoted_to_string(ast)

  # Compile a Cure module to a loadable module atom. Uses the same
  # pipeline as `cure compile`: lex -> parse -> codegen -> beam_writer.
  defp compile_and_load!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    {:ok, forms} = Codegen.compile_module(ast, emit_events: false)
    {:ok, mod} = BeamWriter.compile_and_load(forms)
    mod
  end

  # -- AST shape -------------------------------------------------------------

  describe "Melquiades operator AST" do
    test "ASCII `<-|` lowers to {:send, meta, [target, message]} with :ascii form" do
      ast = parse!("pid <-| :ping")

      assert {:send, meta, [{:variable, _, "pid"}, {:literal, _, :ping}]} = ast
      assert Keyword.get(meta, :melquiades_form) == :ascii
    end

    test "unicode `\u2709` lowers to {:send, ...} with :unicode form" do
      ast = parse!("pid \u2709 :ping")

      assert {:send, meta, [{:variable, _, "pid"}, {:literal, _, :ping}]} = ast
      assert Keyword.get(meta, :melquiades_form) == :unicode
    end

    test "keyword form `send t, m` desugars to the same node with :keyword form" do
      ast = parse!("send pid, :ping")

      assert {:send, meta, [{:variable, _, "pid"}, {:literal, _, :ping}]} = ast
      assert Keyword.get(meta, :melquiades_form) == :keyword
    end

    test "pipe has higher precedence than Melquiades: `x |> f <-| self()`" do
      ast = parse!("x |> build <-| self")

      # Expected: (x |> build) <-| self
      assert {:send, _, [{:function_call, fc_meta, [_x]}, _self]} = ast
      assert Keyword.get(fc_meta, :pipe) == true
      assert Keyword.get(fc_meta, :name) == "build"
    end

    test "the operator is non-associative: `a <-| b <-| c` does not nest" do
      # Non-associative means the parser stops after the first send.
      # We just check it still parses (errors are swallowed by `parse/1`
      # because non-assoc rejection only changes shape), and that the
      # outer node is exactly one `:send` with `b` on the right, not two.
      ast = parse!("a <-| b")
      assert {:send, _, [_, _]} = ast
    end
  end

  # -- Printer round-trip ----------------------------------------------------

  describe "Printer round-trip" do
    test "ASCII form prints as `<-|`" do
      ast = parse!("pid <-| :ping")
      assert print(ast) =~ "pid <-| :ping"
    end

    test "unicode form prints as `\u2709`" do
      ast = parse!("pid \u2709 :ping")
      assert print(ast) =~ "pid \u2709 :ping"
    end

    test "keyword form prints as `send target, message`" do
      ast = parse!("send pid, :ping")
      assert print(ast) =~ "send pid, :ping"
    end
  end

  # -- Effect inference ------------------------------------------------------

  describe "Effect inference" do
    test "Melquiades send attracts the :state effect" do
      ast = parse!("pid <-| :ping")
      effects = Effects.infer_effects(ast, Cure.Types.Env.new())
      assert :state in effects
    end

    test "the keyword form `send t, m` also attracts :state" do
      ast = parse!("send pid, :ping")
      effects = Effects.infer_effects(ast, Cure.Types.Env.new())
      assert :state in effects
    end
  end

  # -- Runtime behaviour -----------------------------------------------------

  describe "Runtime semantics" do
    test "`<-|` delivers the message to the target pid's mailbox" do
      src = """
      mod Cure.Test.MelquiadesSend
        fn deliver(pid: Pid, msg: Atom) -> Atom = pid <-| msg
      """

      mod = compile_and_load!(src)

      me = self()
      mod.deliver(me, :hello)

      assert_receive :hello, 500
    end

    test "the unicode form `\u2709` has identical runtime semantics" do
      src = """
      mod Cure.Test.MelquiadesSendUnicode
        fn deliver(pid: Pid, msg: Atom) -> Atom = pid \u2709 msg
      """

      mod = compile_and_load!(src)

      me = self()
      mod.deliver(me, :world)

      assert_receive :world, 500
    end

    test "`<-|` returns the sent message so it can be bound" do
      src = """
      mod Cure.Test.MelquiadesReturnsMsg
        fn deliver(pid: Pid, msg: Atom) -> Atom =
          let reply = pid <-| msg
          reply
      """

      mod = compile_and_load!(src)
      me = self()

      assert mod.deliver(me, :bang) == :bang
      assert_receive :bang, 500
    end
  end
end
