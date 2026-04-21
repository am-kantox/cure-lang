defmodule :cure_std_regex_test do
  use ExUnit.Case, async: true

  describe "compile/1 and compile_bang/1" do
    test "compile wraps a valid pattern" do
      assert {:ok, %{__struct__: :regex, handle: _}} = :cure_std_regex.compile("a+")
    end

    test "compile returns InvalidPattern for a bad regex" do
      assert {:error, {:invalid_pattern, _msg}} = :cure_std_regex.compile("a(")
    end

    test "compile returns InvalidPattern for non-binary input" do
      assert {:error, {:invalid_pattern, _}} = :cure_std_regex.compile(42)
    end

    test "compile_bang raises on a bad pattern" do
      assert_raise ArgumentError, ~r/invalid regex/, fn ->
        :cure_std_regex.compile_bang("[abc")
      end
    end
  end

  describe "is_match/2" do
    test "matches a compiled regex" do
      {:ok, r} = :cure_std_regex.compile("h.*o")
      assert :cure_std_regex.is_match(r, "hello")
      refute :cure_std_regex.is_match(r, "byee")
    end

    test "accepts a raw pattern string" do
      assert :cure_std_regex.is_match("[0-9]+", "abc123")
      refute :cure_std_regex.is_match("[0-9]+", "abc")
    end

    test "returns false for non-binary input" do
      {:ok, r} = :cure_std_regex.compile(".+")
      refute :cure_std_regex.is_match(r, 42)
    end
  end

  describe "run/2" do
    test "returns the first match with capture groups" do
      {:ok, r} = :cure_std_regex.compile("(\\w+)\\s(\\w+)")

      assert {:some, %{__struct__: :matched, whole: "hello world", groups: ["hello", "world"]}} =
               :cure_std_regex.run(r, "hello world, again")
    end

    test "returns :none when nothing matches" do
      {:ok, r} = :cure_std_regex.compile("^\\d+$")
      assert :cure_std_regex.run(r, "abc") == :none
    end
  end

  describe "scan/2" do
    test "returns every match in source order" do
      {:ok, r} = :cure_std_regex.compile("\\d+")
      matches = :cure_std_regex.scan(r, "1, then 22, then 333.")
      assert [%{whole: "1"}, %{whole: "22"}, %{whole: "333"}] = matches
    end

    test "returns [] when nothing matches" do
      {:ok, r} = :cure_std_regex.compile("x")
      assert :cure_std_regex.scan(r, "abcd") == []
    end
  end

  describe "replace/3" do
    test "replaces every match" do
      {:ok, r} = :cure_std_regex.compile("foo")
      assert :cure_std_regex.replace(r, "foo bar foo baz", "QUX") == "QUX bar QUX baz"
    end

    test "supports backreferences" do
      {:ok, r} = :cure_std_regex.compile("(\\w+)=(\\w+)")

      assert :cure_std_regex.replace(r, "a=1 b=2", "\\2:\\1") == "1:a 2:b"
    end
  end

  describe "split/2" do
    test "splits on every match" do
      {:ok, r} = :cure_std_regex.compile("\\s*,\\s*")
      assert :cure_std_regex.split(r, "a,b , c, d") == ["a", "b", "c", "d"]
    end

    test "returns the input as a one-element list when regex is invalid" do
      assert :cure_std_regex.split(:junk, "abc") == ["abc"]
    end
  end
end
