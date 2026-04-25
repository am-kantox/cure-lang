defmodule Cure.Doc.AsciiTest do
  use ExUnit.Case, async: true

  alias Cure.Doc.Ascii

  # The renderer is fed AST nodes directly so the tests stay decoupled
  # from the parser and from any specific example file.

  describe "render/2 -- FSM" do
    test "emits header, states, and a transition table" do
      transitions = [
        {:function_call, [name: "transition", from: "Locked", event: "coin", to: "Unlocked", event_kind: :normal], []},
        {:function_call, [name: "transition", from: "Unlocked", event: "push", to: "Locked", event_kind: :normal], []}
      ]

      ast = {:container, [container_type: :fsm, name: "Turnstile", line: 1], transitions}

      out = Ascii.render(ast)
      assert is_binary(out)
      assert out =~ "fsm Turnstile"
      assert out =~ "states:"
      assert out =~ "▢ Locked"
      assert out =~ "▢ Unlocked"
      assert out =~ "transitions:"
      assert out =~ "Locked ──[coin]──> Unlocked"
      assert out =~ "Unlocked ──[push]──> Locked"
    end

    test "preserves event suffixes ! and ?" do
      transitions = [
        {:function_call, [name: "transition", from: "S0", event: "go", to: "S1", event_kind: :hard], []},
        {:function_call, [name: "transition", from: "S1", event: "skip", to: "S0", event_kind: :soft], []}
      ]

      ast = {:container, [container_type: :fsm, name: "X", line: 1], transitions}
      out = Ascii.render(ast)

      assert out =~ "[go!]"
      assert out =~ "[skip?]"
    end

    test "marks terminal states with a filled glyph and a -->* line" do
      transitions = [
        {:function_call, [name: "transition", from: "S0", event: "stop", to: "Done", event_kind: :normal], []}
      ]

      ast =
        {:container, [container_type: :fsm, name: "Y", terminal_states: ["Done"], line: 1], transitions}

      out = Ascii.render(ast)
      assert out =~ "▣ Done"
      assert out =~ "Done ──> *"
    end
  end

  describe "render/2 -- Supervisor" do
    test "vertical tree with restart policies" do
      children = [
        {:sup_child, [id: "worker", module: "Cure.Actor.Worker", restart: :permanent], []},
        {:sup_child, [id: "echo", module: "Cure.Actor.Echo", restart: :transient], []}
      ]

      ast =
        {:container, [container_type: :sup, name: "Colony", strategy: :one_for_one, line: 1], children}

      out = Ascii.render(ast)
      assert out =~ "sup Colony (strategy: one_for_one)"
      assert out =~ "├── worker :: Cure.Actor.Worker (permanent)"
      assert out =~ "└── echo :: Cure.Actor.Echo (transient)"
    end
  end

  describe "render/2 -- Application" do
    test "panel includes vsn, root, applications" do
      ast =
        {:container,
         [
           container_type: :app,
           name: "Forge",
           vsn: "0.1.0",
           description: "demo",
           root: "Forge.Root",
           applications: [:logger, :stdlib],
           line: 1
         ], []}

      out = Ascii.render(ast)
      assert out =~ "app Forge (vsn 0.1.0)"
      assert out =~ "description: demo"
      assert out =~ "root: Forge.Root"
      assert out =~ "applications:"
      assert out =~ "├── logger"
      assert out =~ "├── stdlib"
    end
  end

  describe "render/2 -- non-diagram containers" do
    test "returns nil for plain modules" do
      ast = {:container, [container_type: :module, name: "Plain", line: 1], []}
      assert Ascii.render(ast) == nil
    end

    test "returns nil for non-container nodes" do
      assert Ascii.render({:literal, [], 0}) == nil
    end
  end

  describe "render_file/2" do
    test "round-trips a source file via the parser" do
      src = """
      mod Demo
        fn ok() -> Atom = :ok
      """

      path =
        Path.join(System.tmp_dir!(), "cure_ascii_test_#{System.unique_integer([:positive])}.cure")

      try do
        File.write!(path, src)
        assert {:ok, ""} = Ascii.render_file(path)
      after
        File.rm!(path)
      end
    end
  end
end
