defmodule Cure.REPL.TerminalTest do
  use ExUnit.Case, async: true

  alias Cure.REPL.Terminal

  describe "decode/1" do
    test "plain printable byte" do
      assert {:key, "a"} = Terminal.decode("a")
    end

    test "ctrl codes" do
      assert {:ctrl, ?A} = Terminal.decode(<<1>>)
      assert {:ctrl, ?E} = Terminal.decode(<<5>>)
    end

    test "enter / backspace / tab" do
      assert :enter = Terminal.decode(<<13>>)
      assert :enter = Terminal.decode(<<10>>)
      assert :backspace = Terminal.decode(<<127>>)
      assert :tab = Terminal.decode(<<9>>)
    end

    test "arrow keys via CSI" do
      assert :up = Terminal.decode("\e[A")
      assert :down = Terminal.decode("\e[B")
      assert :right = Terminal.decode("\e[C")
      assert :left = Terminal.decode("\e[D")
    end

    test "home/end via CSI short forms" do
      assert :home = Terminal.decode("\e[H")
      assert :end = Terminal.decode("\e[F")
    end

    test "tilde-terminated keys" do
      assert :delete = Terminal.decode("\e[3~")
      assert :pgup = Terminal.decode("\e[5~")
      assert :pgdn = Terminal.decode("\e[6~")
      assert {:fn, 5} = Terminal.decode("\e[15~")
    end

    test "modifier sequences" do
      assert :word_right = Terminal.decode("\e[1;5C")
      assert :word_left = Terminal.decode("\e[1;5D")
    end

    test "alt-prefixed chars" do
      assert {:alt, "b"} = Terminal.decode("\eb")
      assert {:alt, "f"} = Terminal.decode("\ef")
    end

    test "SS3 alternative forms" do
      assert :up = Terminal.decode("\eOA")
      assert {:fn, 1} = Terminal.decode("\eOP")
    end
  end
end
