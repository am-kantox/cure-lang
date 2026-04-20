defmodule Cure.REPL.LineEditorTest do
  use ExUnit.Case, async: true

  alias Cure.REPL.LineEditor, as: LE

  describe "insertion and movement" do
    test "insert text advances cursor" do
      ed = LE.new() |> LE.insert("hello")
      assert ed.buffer == "hello"
      assert ed.cursor == 5
    end

    test "home/end jump" do
      ed = LE.new() |> LE.insert("abc")
      assert LE.move_home(ed).cursor == 0
      assert LE.move_end(LE.move_home(ed)).cursor == 3
    end

    test "left/right clamp at boundaries" do
      ed = LE.new() |> LE.insert("ab")
      assert LE.move_left(LE.move_left(LE.move_left(ed))).cursor == 0
      assert LE.move_right(LE.move_right(LE.move_right(ed))).cursor == 2
    end

    test "word-wise movement respects non-word graphemes" do
      ed = %{LE.new() | buffer: "foo bar baz", cursor: 11}
      ed2 = LE.move_word_left(ed)
      assert ed2.cursor == 8
      ed3 = LE.move_word_left(ed2)
      assert ed3.cursor == 4
      ed4 = LE.move_word_right(LE.move_home(ed))
      assert ed4.cursor == 3
    end
  end

  describe "deletion" do
    test "backspace removes preceding grapheme" do
      ed = LE.new() |> LE.insert("abc") |> LE.backspace()
      assert ed.buffer == "ab"
      assert ed.cursor == 2
    end

    test "delete_char removes under cursor" do
      ed = %{LE.new() | buffer: "abc", cursor: 1}
      ed2 = LE.delete_char(ed)
      assert ed2.buffer == "ac"
      assert ed2.cursor == 1
    end

    test "kill_to_end pushes removed text to kill ring" do
      ed = %{LE.new() | buffer: "foo bar", cursor: 3}
      ed2 = LE.kill_to_end(ed)
      assert ed2.buffer == "foo"
      assert [" bar" | _] = ed2.kill_ring
    end

    test "kill_word_back deletes previous word and stores it" do
      ed = %{LE.new() | buffer: "hello world", cursor: 11}
      ed2 = LE.kill_word_back(ed)
      assert ed2.buffer == "hello "
      assert ["world" | _] = ed2.kill_ring
    end
  end

  describe "yank" do
    test "yank re-inserts most recent kill" do
      ed = %{LE.new() | buffer: "foo", cursor: 3}
      ed2 = LE.kill_to_start(ed)
      ed3 = LE.yank(ed2)
      assert ed3.buffer == "foo"
    end
  end

  describe "transpose" do
    test "transpose chars in middle of buffer" do
      ed = %{LE.new() | buffer: "abc", cursor: 2}
      ed2 = LE.transpose_chars(ed)
      assert ed2.buffer == "acb"
    end

    test "transpose chars at end of buffer swaps last two" do
      ed = %{LE.new() | buffer: "ab", cursor: 2}
      ed2 = LE.transpose_chars(ed)
      assert ed2.buffer == "ba"
    end
  end

  describe "undo/redo" do
    test "undo reverts last insertion" do
      ed = LE.new() |> LE.insert("hi") |> LE.insert("!")
      assert ed.buffer == "hi!"
      ed2 = LE.undo(ed)
      assert ed2.buffer == "hi"
      ed3 = LE.redo(ed2)
      assert ed3.buffer == "hi!"
    end
  end

  describe "handle/2 dispatch" do
    test "enter emits :submit signal" do
      ed = LE.new() |> LE.insert("foo")
      assert {:signal, :submit, ^ed} = LE.handle(ed, :enter)
    end

    test "ctrl+D on empty buffer signals EOF" do
      assert {:signal, :eof, _} = LE.handle(LE.new(), {:ctrl, ?D})
    end

    test "ctrl+C aborts and resets buffer" do
      ed = LE.new() |> LE.insert("pending")
      assert {:signal, :abort, %LE{buffer: ""}} = LE.handle(ed, {:ctrl, ?C})
    end

    test "plain key insertion updates buffer" do
      {:cont, ed} = LE.handle(LE.new(), {:key, "a"})
      assert ed.buffer == "a"
    end

    test "paste inserts the entire chunk in one go" do
      {:cont, ed} = LE.handle(LE.new(), {:paste, "hello\nworld"})
      assert ed.buffer == "hello\nworld"
    end
  end

  describe "vi mode" do
    test "i/a toggle back to insert" do
      ed = %{LE.new() | mode: :vi_normal, buffer: "abc", cursor: 1}
      assert {:cont, %LE{mode: :vi_insert}} = LE.handle(ed, {:key, "i"})
      assert {:cont, %LE{mode: :vi_insert, cursor: 2}} = LE.handle(ed, {:key, "a"})
    end

    test "x deletes char under cursor" do
      ed = %{LE.new() | mode: :vi_normal, buffer: "abc", cursor: 1}
      {:cont, ed2} = LE.handle(ed, {:key, "x"})
      assert ed2.buffer == "ac"
    end
  end
end
