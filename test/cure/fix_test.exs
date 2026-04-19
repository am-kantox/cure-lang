defmodule Cure.FixTest do
  use ExUnit.Case, async: true

  alias Cure.Fix

  setup do
    tmp = Path.join(System.tmp_dir!(), "cure_fix_#{:erlang.unique_integer([:positive])}")
    File.mkdir_p!(Path.join(tmp, "lib"))
    on_exit(fn -> File.rm_rf!(tmp) end)
    {:ok, root: tmp}
  end

  test "strips trailing whitespace from a file", %{root: root} do
    file = Path.join([root, "lib", "sample.cure"])
    File.write!(file, "mod Foo   \n  fn bar() -> Int = 1   \n")

    [%{file: ^file, changed?: true, applied: applied}] =
      Fix.run(root)

    assert :strip_trailing_whitespace in applied
    assert File.read!(file) == "mod Foo\n  fn bar() -> Int = 1\n"
  end

  test "collapses runs of blank lines", %{root: root} do
    file = Path.join([root, "lib", "blanks.cure"])
    File.write!(file, "mod A\n\n\n\n  fn f() -> Int = 1\n")

    [%{file: ^file, changed?: true, applied: applied}] = Fix.run(root)
    assert :collapse_blank_lines in applied
    refute File.read!(file) =~ ~r/\n{3,}/
  end

  test "dry run does not write", %{root: root} do
    file = Path.join([root, "lib", "dry.cure"])
    original = "mod B    \n"
    File.write!(file, original)

    [%{changed?: true}] = Fix.run(root, dry_run: true)
    assert File.read!(file) == original
  end

  test "leaves already-clean files alone", %{root: root} do
    file = Path.join([root, "lib", "clean.cure"])
    File.write!(file, "mod Clean\n  fn f() -> Int = 1\n")

    [%{changed?: false, applied: []}] = Fix.run(root)
  end
end
