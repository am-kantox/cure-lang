defmodule Cure.Project.JsonTest do
  use ExUnit.Case, async: true

  alias Cure.Project.Json

  describe "encode/1 -- primitives" do
    test "nil / true / false" do
      assert Json.encode(nil) == "null"
      assert Json.encode(true) == "true"
      assert Json.encode(false) == "false"
    end

    test "integers and floats" do
      assert Json.encode(42) == "42"
      assert Json.encode(-7) == "-7"
      assert Json.encode(1.5) == "1.5"
    end

    test "strings are quoted and escaped" do
      assert Json.encode("hello") == ~s("hello")
      assert Json.encode("he said \"hi\"") == ~s("he said \\"hi\\"")
      assert Json.encode("line\nbreak") == ~s("line\\nbreak")
    end

    test "atoms become strings" do
      assert Json.encode(:foo) == ~s("foo")
    end
  end

  describe "encode/1 -- containers" do
    test "empty array / object" do
      assert Json.encode([]) == "[]"
      assert Json.encode(%{}) == "{}"
    end

    test "flat array" do
      assert Json.encode([1, 2, 3]) == "[1,2,3]"
    end

    test "object with string keys" do
      assert Json.encode(%{"a" => 1}) == ~s({"a":1})
    end

    test "nested structures" do
      payload = %{"xs" => [1, 2], "meta" => %{"ok" => true}}
      assert {:ok, ^payload} = payload |> Json.encode() |> Json.decode()
    end
  end

  describe "decode/1 -- happy paths" do
    test "decodes scalars" do
      assert {:ok, nil} = Json.decode("null")
      assert {:ok, true} = Json.decode("true")
      assert {:ok, false} = Json.decode("false")
      assert {:ok, 42} = Json.decode("42")
      assert {:ok, 1.5} = Json.decode("1.5")
      assert {:ok, "hi"} = Json.decode(~s("hi"))
    end

    test "decodes arrays and objects" do
      assert {:ok, [1, 2, 3]} = Json.decode("[1, 2, 3]")
      assert {:ok, %{"a" => 1, "b" => [2, 3]}} = Json.decode(~s({"a":1,"b":[2,3]}))
    end

    test "round-trips a registry-shaped manifest" do
      manifest = %{
        "name" => "example",
        "version" => "0.1.0",
        "dependencies" => [%{"name" => "dep", "constraint" => "~> 1.0"}]
      }

      assert {:ok, ^manifest} = manifest |> Json.encode() |> Json.decode()
    end

    test "whitespace is ignored" do
      assert {:ok, %{"k" => 1}} = Json.decode(~s(   { "k"  :   1  }  ))
    end
  end

  describe "decode/1 -- error cases" do
    test "unterminated string" do
      assert {:error, {:unterminated_string, _}} = Json.decode(~s("abc))
    end

    test "trailing data" do
      assert {:error, {:trailing_data, _}} = Json.decode("1 xyz")
    end

    test "unexpected EOF inside object" do
      assert {:error, {:unexpected_eof, _}} = Json.decode("{")
    end

    test "invalid token" do
      assert {:error, {:invalid_token, _}} = Json.decode("nope")
    end
  end
end
