defmodule Cure.Term.HyperlinkTest do
  use ExUnit.Case, async: false

  alias Cure.Term.Hyperlink

  # The emit? gate reads the process/OS environment. Every test that
  # depends on a specific outcome locks the relevant environment
  # variables and restores them on exit.

  setup do
    previous = %{
      "TERM" => System.get_env("TERM"),
      "NO_COLOR" => System.get_env("NO_COLOR"),
      "CURE_HYPERLINKS" => System.get_env("CURE_HYPERLINKS")
    }

    on_exit(fn ->
      Enum.each(previous, fn
        {k, nil} -> System.delete_env(k)
        {k, v} -> System.put_env(k, v)
      end)
    end)

    :ok
  end

  describe "emit?/0" do
    test "is false when NO_COLOR is set" do
      System.put_env("NO_COLOR", "1")
      System.put_env("CURE_HYPERLINKS", "1")
      System.put_env("TERM", "xterm-kitty")
      refute Hyperlink.emit?()
    end

    test "is false when CURE_HYPERLINKS=0" do
      System.delete_env("NO_COLOR")
      System.put_env("CURE_HYPERLINKS", "0")
      System.put_env("TERM", "xterm-kitty")
      refute Hyperlink.emit?()
    end

    test "is true when CURE_HYPERLINKS=1 overrides everything else" do
      System.delete_env("NO_COLOR")
      System.put_env("CURE_HYPERLINKS", "1")
      # Even if TERM is dumb, the explicit opt-in wins.
      System.put_env("TERM", "dumb")
      assert Hyperlink.emit?()
    end

    test "is true for xterm-kitty when ANSI is forced on" do
      System.delete_env("NO_COLOR")
      System.put_env("CURE_HYPERLINKS", "yes")
      System.put_env("TERM", "xterm-kitty")
      assert Hyperlink.emit?()
    end

    test "is false for dumb terminals even with ANSI on" do
      System.delete_env("NO_COLOR")
      System.delete_env("CURE_HYPERLINKS")
      System.put_env("TERM", "dumb")
      refute Hyperlink.emit?()
    end
  end

  describe "wrap/2" do
    test "passes the label through when emission is disabled" do
      System.put_env("CURE_HYPERLINKS", "0")
      assert Hyperlink.wrap("file:///tmp/x", "label") == "label"
    end

    test "wraps the label in an OSC 8 sequence when emission is forced on" do
      System.put_env("CURE_HYPERLINKS", "1")
      System.delete_env("NO_COLOR")
      out = Hyperlink.wrap("file:///tmp/x", "label")

      assert out ==
               "\e]8;;file:///tmp/x\e\\label\e]8;;\e\\"
    end
  end

  describe "file_link/2" do
    test "degrades to the visible label when emission is disabled" do
      System.put_env("CURE_HYPERLINKS", "0")
      assert Hyperlink.file_link("rel/path.cure") == "rel/path.cure"
    end

    test "returns the label unchanged for placeholder files" do
      System.put_env("CURE_HYPERLINKS", "1")
      System.delete_env("NO_COLOR")
      assert Hyperlink.file_link("nofile") == "nofile"
      assert Hyperlink.file_link("") == ""
    end

    test "emits an OSC 8 link with absolute file URI for a relative path" do
      System.put_env("CURE_HYPERLINKS", "1")
      System.delete_env("NO_COLOR")

      out = Hyperlink.file_link("some/thing.cure")
      cwd = File.cwd!()
      expected_uri = "file://" <> cwd <> "/some/thing.cure"

      assert out =~ "\e]8;;" <> expected_uri <> "\e\\"
      assert out =~ "some/thing.cure"
      assert String.ends_with?(out, "\e]8;;\e\\")
    end
  end

  describe "file_line_link/3" do
    test "appends #L<line> to the URI when line is positive" do
      System.put_env("CURE_HYPERLINKS", "1")
      System.delete_env("NO_COLOR")

      out = Hyperlink.file_line_link("/abs/path.cure", 42)

      assert out =~ "#L42\e\\"
      assert out =~ "/abs/path.cure:42"
    end

    test "appends #L<line>C<col> when both are positive" do
      System.put_env("CURE_HYPERLINKS", "1")
      System.delete_env("NO_COLOR")

      out = Hyperlink.file_line_link("/abs/path.cure", 12, col: 7)
      assert out =~ "#L12C7\e\\"
    end

    test "emits a bare file:// URI when line is zero" do
      System.put_env("CURE_HYPERLINKS", "1")
      System.delete_env("NO_COLOR")

      out = Hyperlink.file_line_link("/abs/path.cure", 0)
      refute out =~ "#L"
      assert out =~ "file:///abs/path.cure\e\\"
    end

    test "percent-encodes spaces in the URI but keeps them in the label" do
      System.put_env("CURE_HYPERLINKS", "1")
      System.delete_env("NO_COLOR")

      out = Hyperlink.file_line_link("/abs/with space.cure", 3)
      # URI half:
      assert out =~ "file:///abs/with%20space.cure#L3"
      # Label half (the human-readable path still has the space):
      assert out =~ "/abs/with space.cure:3"
    end

    test "returns the plain label when emission is disabled" do
      System.put_env("CURE_HYPERLINKS", "0")
      assert Hyperlink.file_line_link("/abs/path.cure", 7) == "/abs/path.cure:7"
    end
  end
end
