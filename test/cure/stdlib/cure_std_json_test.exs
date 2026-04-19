defmodule :cure_std_json_test do
  use ExUnit.Case, async: true

  describe "encode/1" do
    test "encodes scalars" do
      assert :cure_std_json.encode(:null) == "null"
      assert :cure_std_json.encode({:bool, true}) == "true"
      assert :cure_std_json.encode({:bool, false}) == "false"
      assert :cure_std_json.encode({:num, 1.0}) == "1.0"
      assert :cure_std_json.encode({:str, "hi"}) == ~s("hi")
    end

    test "encodes arrays and objects" do
      assert :cure_std_json.encode({:arr, [{:num, 1.0}, {:num, 2.0}]}) == "[1.0,2.0]"
      assert :cure_std_json.encode({:obj, [{"a", {:num, 1.0}}]}) == ~s({"a":1.0})
    end
  end

  describe "decode/1" do
    test "parses valid JSON into the Value ADT" do
      assert {:ok, {:obj, _}} = :cure_std_json.decode(~s({"a":1,"b":[true, null, "s"]}))
    end

    test "returns an error string on bad input" do
      assert {:error, _msg} = :cure_std_json.decode("{bogus")
    end
  end

  describe "num_of_int/1" do
    test "widens an integer to a Num Value" do
      assert {:num, 5.0} = :cure_std_json.num_of_int(5)
    end
  end
end
