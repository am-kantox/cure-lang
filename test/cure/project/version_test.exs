defmodule Cure.Project.VersionTest do
  use ExUnit.Case, async: true

  alias Cure.Project.Version

  describe "parse/1" do
    test "parses MAJOR.MINOR.PATCH" do
      assert {:ok, {1, 2, 3, nil}} = Version.parse("1.2.3")
      assert {:ok, {0, 17, 1, nil}} = Version.parse("0.17.1")
    end

    test "parses pre-release suffix" do
      assert {:ok, {1, 0, 0, "alpha"}} = Version.parse("1.0.0-alpha")
      assert {:ok, {1, 0, 0, "rc.1"}} = Version.parse("1.0.0-rc.1")
    end

    test "strips build metadata" do
      assert {:ok, {1, 0, 0, nil}} = Version.parse("1.0.0+sha.abc123")
    end

    test "accepts MAJOR.MINOR as shorthand for MAJOR.MINOR.0" do
      assert {:ok, {1, 2, 0, nil}} = Version.parse("1.2")
      assert {:ok, {1, 0, 0, nil}} = Version.parse("1.0")
    end

    test "rejects malformed input" do
      assert {:error, _} = Version.parse("not-a-version")
      assert {:error, _} = Version.parse("")
      assert {:error, _} = Version.parse("1")
    end
  end

  describe "compare/2" do
    test "orders by major/minor/patch" do
      assert Version.compare({1, 0, 0, nil}, {2, 0, 0, nil}) == :lt
      assert Version.compare({1, 2, 0, nil}, {1, 2, 0, nil}) == :eq
      assert Version.compare({1, 2, 3, nil}, {1, 2, 2, nil}) == :gt
    end

    test "pre-release is less than no pre-release at same base" do
      assert Version.compare({1, 0, 0, "rc.1"}, {1, 0, 0, nil}) == :lt
      assert Version.compare({1, 0, 0, nil}, {1, 0, 0, "rc.1"}) == :gt
    end
  end

  describe "parse_constraint/1" do
    test "parses a single comparison" do
      assert {:ok, [{:~>, {1, 0, 0, nil}}]} = Version.parse_constraint("~> 1.0.0")
      assert {:ok, [{:>=, {2, 0, 0, nil}}]} = Version.parse_constraint(">= 2.0.0")
    end

    test "parses compound constraints joined by `and`" do
      assert {:ok, [{:>=, {1, 0, 0, nil}}, {:<, {1, 5, 0, nil}}]} =
               Version.parse_constraint(">= 1.0.0 and < 1.5.0")
    end

    test "defaults to equality when no operator is given" do
      assert {:ok, [{:==, {1, 2, 3, nil}}]} = Version.parse_constraint("1.2.3")
    end
  end

  describe "satisfies?/2" do
    test "~> matches within the same MAJOR" do
      c = [{:~>, {1, 2, 0, nil}}]
      assert Version.satisfies?({1, 2, 3, nil}, c)
      assert Version.satisfies?({1, 9, 9, nil}, c)
      refute Version.satisfies?({2, 0, 0, nil}, c)
      refute Version.satisfies?({1, 1, 9, nil}, c)
    end

    test ">=, <=, >, <, == work as expected" do
      assert Version.satisfies?({2, 0, 0, nil}, [{:>=, {1, 0, 0, nil}}])
      assert Version.satisfies?({1, 0, 0, nil}, [{:<=, {1, 0, 0, nil}}])
      assert Version.satisfies?({1, 0, 1, nil}, [{:>, {1, 0, 0, nil}}])
      assert Version.satisfies?({0, 9, 9, nil}, [{:<, {1, 0, 0, nil}}])
      assert Version.satisfies?({1, 0, 0, nil}, [{:==, {1, 0, 0, nil}}])
      refute Version.satisfies?({1, 0, 1, nil}, [{:==, {1, 0, 0, nil}}])
    end

    test "compound constraints require every clause" do
      c = [{:>=, {1, 0, 0, nil}}, {:<, {2, 0, 0, nil}}]
      assert Version.satisfies?({1, 5, 0, nil}, c)
      refute Version.satisfies?({2, 0, 0, nil}, c)
      refute Version.satisfies?({0, 9, 9, nil}, c)
    end
  end
end
