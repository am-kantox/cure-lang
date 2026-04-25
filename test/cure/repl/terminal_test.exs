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

    test "alt+enter (ESC + CR/LF) decodes as :alt_enter" do
      assert :alt_enter = Terminal.decode("\e\r")
      assert :alt_enter = Terminal.decode("\e\n")
    end

    test "CSI-u modified Enter decodes as :alt_enter" do
      # Shift+Enter, Alt+Enter, Ctrl+Enter, Ctrl+Shift+Enter, ...
      assert :alt_enter = Terminal.decode("\e[13;2u")
      assert :alt_enter = Terminal.decode("\e[13;3u")
      assert :alt_enter = Terminal.decode("\e[13;5u")
      assert :alt_enter = Terminal.decode("\e[13;6u")
    end

    test "unmodified CSI-u Enter (\\e[13u) is still :enter" do
      assert :enter = Terminal.decode("\e[13u")
    end

    test "xterm modifyOtherKeys form decodes modified Enter as :alt_enter" do
      assert :alt_enter = Terminal.decode("\e[27;2;13~")
      assert :alt_enter = Terminal.decode("\e[27;5;13~")
      assert :alt_enter = Terminal.decode("\e[27;5;10~")
    end
  end
end
