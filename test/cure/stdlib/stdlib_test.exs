defmodule Cure.StdlibTest do
  use ExUnit.Case, async: false

  # Helper: compile a stdlib .cure file and load it into the VM
  defp compile_stdlib(name) do
    path = Path.join(["lib", "std", "#{name}.cure"])
    source = File.read!(path)

    case Cure.Compiler.compile_and_load(source, file: path) do
      {:ok, module} -> module
      {:error, reason} -> flunk("Failed to compile #{name}: #{inspect(reason)}")
    end
  end

  defp purge(module) do
    :code.purge(module)
    :code.delete(module)
  end

  # ============================================================================
  # Std.Math
  # ============================================================================

  describe "Std.Math" do
    setup do
      m = compile_stdlib("math")
      on_exit(fn -> purge(m) end)
      %{m: m}
    end

    test "abs", %{m: m} do
      assert m.abs(-5) == 5
      assert m.abs(5) == 5
      assert m.abs(0) == 0
    end

    test "sqrt", %{m: m} do
      assert m.sqrt(16.0) == 4.0
      assert m.sqrt(0.0) == 0.0
    end

    test "pow", %{m: m} do
      assert m.pow(2.0, 10.0) == 1024.0
    end

    test "log functions", %{m: m} do
      assert_in_delta m.log(1.0), 0.0, 0.001
      assert_in_delta m.log2(8.0), 3.0, 0.001
      assert_in_delta m.log10(100.0), 2.0, 0.001
    end

    test "ceil and floor", %{m: m} do
      assert m.ceil(3.2) == 4.0
      assert m.floor(3.9) == 3.0
    end

    test "round", %{m: m} do
      assert m.round(3.6) == 4
      assert m.round(3.4) == 3
    end

    test "pi", %{m: m} do
      assert_in_delta m.pi(), 3.14159, 0.001
    end

    test "max and min", %{m: m} do
      assert m.max(3, 7) == 7
      assert m.max(7, 3) == 7
      assert m.min(3, 7) == 3
      assert m.min(7, 3) == 3
    end

    test "clamp", %{m: m} do
      assert m.clamp(5, 1, 10) == 5
      assert m.clamp(-5, 1, 10) == 1
      assert m.clamp(15, 1, 10) == 10
    end

    test "sign", %{m: m} do
      assert m.sign(5) == 1
      assert m.sign(-5) == -1
      assert m.sign(0) == 0
    end

    test "negate", %{m: m} do
      assert m.negate(5) == -5
      assert m.negate(-3) == 3
    end

    test "is_even and is_odd", %{m: m} do
      assert m.is_even(4) == true
      assert m.is_even(3) == false
      assert m.is_odd(3) == true
      assert m.is_odd(4) == false
    end

    test "safe_div", %{m: m} do
      assert m.safe_div(10, 3) == 3
      assert m.safe_div(10, 0) == 0
    end
  end

  # ============================================================================
  # Std.Io
  # ============================================================================

  describe "Std.Io" do
    setup do
      m = compile_stdlib("io")
      on_exit(fn -> purge(m) end)
      %{m: m}
    end

    test "int_to_string", %{m: m} do
      assert m.int_to_string(42) == "42"
      assert m.int_to_string(-1) == "-1"
    end

    test "atom_to_string", %{m: m} do
      assert m.atom_to_string(:hello) == "hello"
    end

    test "println returns ok", %{m: m} do
      assert m.println("test") == :ok
    end

    test "print returns ok", %{m: m} do
      assert m.print("test") == :ok
    end
  end

  # ============================================================================
  # Std.Core
  # ============================================================================

  describe "Std.Core -- utility functions" do
    setup do
      m = compile_stdlib("core")
      on_exit(fn -> purge(m) end)
      %{m: m}
    end

    test "identity", %{m: m} do
      assert m.identity(42) == 42
      assert m.identity(:hello) == :hello
    end

    test "compose", %{m: m} do
      double = fn x -> x * 2 end
      inc = fn x -> x + 1 end
      f = m.compose(double, inc)
      assert f.(3) == 8
    end

    test "pipe", %{m: m} do
      assert m.pipe(5, fn x -> x * 3 end) == 15
    end

    test "apply", %{m: m} do
      assert m.apply(fn x -> x + 10 end, 5) == 15
    end

    test "const", %{m: m} do
      always_42 = m.const(42)
      assert always_42.(:anything) == 42
    end
  end

  describe "Std.Core -- boolean operations" do
    setup do
      m = compile_stdlib("core")
      on_exit(fn -> purge(m) end)
      %{m: m}
    end

    test "bool_not", %{m: m} do
      assert m.bool_not(true) == false
      assert m.bool_not(false) == true
    end

    test "bool_and", %{m: m} do
      assert m.bool_and(true, true) == true
      assert m.bool_and(true, false) == false
      assert m.bool_and(false, true) == false
    end

    test "bool_or", %{m: m} do
      assert m.bool_or(false, false) == false
      assert m.bool_or(true, false) == true
      assert m.bool_or(false, true) == true
    end

    test "bool_xor", %{m: m} do
      assert m.bool_xor(true, false) == true
      assert m.bool_xor(false, true) == true
      assert m.bool_xor(true, true) == false
      assert m.bool_xor(false, false) == false
    end
  end

  describe "Std.Core -- comparison operations" do
    setup do
      m = compile_stdlib("core")
      on_exit(fn -> purge(m) end)
      %{m: m}
    end

    test "eq and ne", %{m: m} do
      assert m.eq(3, 3) == true
      assert m.eq(3, 4) == false
      assert m.ne(3, 4) == true
    end

    test "lt, le, gt, ge", %{m: m} do
      assert m.lt(3, 5) == true
      assert m.le(3, 3) == true
      assert m.gt(5, 3) == true
      assert m.ge(3, 3) == true
    end

    test "min and max", %{m: m} do
      assert m.min(3, 7) == 3
      assert m.max(3, 7) == 7
    end

    test "clamp", %{m: m} do
      assert m.clamp(5, 1, 10) == 5
      assert m.clamp(-5, 1, 10) == 1
      assert m.clamp(15, 1, 10) == 10
    end
  end

  describe "Std.Core -- Result type" do
    setup do
      m = compile_stdlib("core")
      on_exit(fn -> purge(m) end)
      %{m: m}
    end

    test "ok and error constructors", %{m: m} do
      assert m.ok(5) == {:ok, 5}
      assert m.error(:bad) == {:error, :bad}
    end

    test "is_ok and is_error", %{m: m} do
      assert m.is_ok({:ok, 5}) == true
      assert m.is_ok({:error, :bad}) == false
      assert m.is_error({:error, :bad}) == true
      assert m.is_error({:ok, 5}) == false
    end

    test "unwrap_ok", %{m: m} do
      assert m.unwrap_ok({:ok, 42}, 0) == 42
      assert m.unwrap_ok({:error, :bad}, 0) == 0
    end

    test "unwrap_error", %{m: m} do
      assert m.unwrap_error({:error, :bad}, :default) == :bad
      assert m.unwrap_error({:ok, 42}, :default) == :default
    end

    test "map_ok", %{m: m} do
      assert m.map_ok({:ok, 5}, fn x -> x * 2 end) == {:ok, 10}
      assert m.map_ok({:error, :bad}, fn x -> x * 2 end) == {:error, :bad}
    end

    test "map_error", %{m: m} do
      assert m.map_error({:error, :bad}, fn _ -> :worse end) == {:error, :worse}
      assert m.map_error({:ok, 5}, fn _ -> :worse end) == {:ok, 5}
    end

    test "and_then", %{m: m} do
      assert m.and_then({:ok, 5}, fn x -> {:ok, x + 1} end) == {:ok, 6}
      assert m.and_then({:error, :bad}, fn x -> {:ok, x + 1} end) == {:error, :bad}
    end

    test "or_else", %{m: m} do
      assert m.or_else({:ok, 5}, fn _ -> {:ok, 0} end) == {:ok, 5}
      assert m.or_else({:error, :bad}, fn _ -> {:ok, 0} end) == {:ok, 0}
    end
  end

  describe "Std.Core -- Option type" do
    setup do
      m = compile_stdlib("core")
      on_exit(fn -> purge(m) end)
      %{m: m}
    end

    test "some and none constructors", %{m: m} do
      assert m.some(42) == {:some, 42}
      assert m.none() == {:none}
    end

    test "is_some and is_none", %{m: m} do
      assert m.is_some({:some, 42}) == true
      assert m.is_some({:none}) == false
      assert m.is_none({:none}) == true
      assert m.is_none({:some, 42}) == false
    end

    test "unwrap", %{m: m} do
      assert m.unwrap({:some, 42}, 0) == 42
      assert m.unwrap({:none}, 0) == 0
    end

    test "map_option", %{m: m} do
      assert m.map_option({:some, 5}, fn x -> x * 2 end) == {:some, 10}
      assert m.map_option({:none}, fn x -> x * 2 end) == {:none}
    end

    test "flat_map_option", %{m: m} do
      assert m.flat_map_option({:some, 5}, fn x -> {:some, x * 2} end) == {:some, 10}
      assert m.flat_map_option({:none}, fn x -> {:some, x * 2} end) == {:none}
    end

    test "option_or", %{m: m} do
      assert m.option_or({:some, 42}, 0) == 42
      assert m.option_or({:none}, 0) == 0
    end
  end

  # ============================================================================
  # Std.List
  # ============================================================================

  describe "Std.List" do
    setup do
      m = compile_stdlib("list")
      on_exit(fn -> purge(m) end)
      %{m: m}
    end

    test "length", %{m: m} do
      assert m.length([]) == 0
      assert m.length([1, 2, 3]) == 3
    end

    test "is_empty", %{m: m} do
      assert m.is_empty([]) == true
      assert m.is_empty([1]) == false
    end

    test "head", %{m: m} do
      assert m.head([1, 2, 3], 0) == 1
      assert m.head([], 0) == 0
    end

    test "tail", %{m: m} do
      assert [_, _] = m.tail([1, 2, 3])
      assert m.tail([]) == []
    end

    test "last", %{m: m} do
      assert m.last([1, 2, 3], 0) == 3
      assert m.last([], 0) == 0
    end

    test "cons", %{m: m} do
      assert [_, _, _] = m.cons(0, [1, 2])
      assert m.cons(0, [1, 2]) == [0, 1, 2]
    end

    test "append", %{m: m} do
      assert m.append([1, 2], [3, 4]) == [1, 2, 3, 4]
      assert m.append([], [1]) == [1]
      assert m.append([1], []) == [1]
    end

    test "concat", %{m: m} do
      assert m.concat([[1, 2], [3], [4, 5]]) == [1, 2, 3, 4, 5]
      assert m.concat([]) == []
    end

    test "reverse", %{m: m} do
      assert m.reverse([1, 2, 3]) == [3, 2, 1]
      assert m.reverse([]) == []
    end

    test "map", %{m: m} do
      assert m.map([1, 2, 3], fn x -> x * 2 end) == [2, 4, 6]
      assert m.map([], fn x -> x end) == []
    end

    test "filter", %{m: m} do
      assert m.filter([1, 2, 3, 4], fn x -> rem(x, 2) == 0 end) == [2, 4]
      assert m.filter([], fn _ -> true end) == []
    end

    test "foldl", %{m: m} do
      # sum via fold
      assert m.foldl([1, 2, 3], 0, fn x -> fn a -> a + x end end) == 6
    end

    test "foldr", %{m: m} do
      # cons via foldr builds the list in order
      result = m.foldr([1, 2, 3], [], fn x -> fn acc -> [x | acc] end end)
      assert result == [1, 2, 3]
    end

    test "flat_map", %{m: m} do
      assert m.flat_map([1, 2, 3], fn x -> [x, x * 10] end) == [1, 10, 2, 20, 3, 30]
    end

    test "zip_with", %{m: m} do
      result = m.zip_with([1, 2, 3], [10, 20, 30], fn a -> fn b -> a + b end end)
      assert result == [11, 22, 33]
    end

    test "nth", %{m: m} do
      assert m.nth([10, 20, 30], 0, -1) == 10
      assert m.nth([10, 20, 30], 2, -1) == 30
      assert m.nth([10, 20, 30], 5, -1) == -1
    end

    test "take", %{m: m} do
      assert m.take([1, 2, 3, 4, 5], 3) == [1, 2, 3]
      assert m.take([1, 2], 5) == [1, 2]
      assert m.take([1, 2, 3], 0) == []
    end

    test "drop", %{m: m} do
      assert m.drop([1, 2, 3, 4, 5], 2) == [3, 4, 5]
      assert m.drop([1, 2], 5) == []
      assert m.drop([1, 2, 3], 0) == [1, 2, 3]
    end

    test "contains", %{m: m} do
      assert m.contains([1, 2, 3], 2) == true
      assert m.contains([1, 2, 3], 5) == false
      assert m.contains([], 1) == false
    end

    test "find", %{m: m} do
      assert m.find([1, 2, 3, 4], fn x -> x > 2 end, -1) == 3
      assert m.find([1, 2], fn x -> x > 5 end, -1) == -1
    end

    test "any", %{m: m} do
      assert m.any([1, 2, 3], fn x -> x > 2 end) == true
      assert m.any([1, 2, 3], fn x -> x > 5 end) == false
    end

    test "all", %{m: m} do
      assert m.all([1, 2, 3], fn x -> x > 0 end) == true
      assert m.all([1, 2, 3], fn x -> x > 1 end) == false
    end

    test "sum", %{m: m} do
      assert m.sum([1, 2, 3, 4, 5]) == 15
      assert m.sum([]) == 0
    end

    test "product", %{m: m} do
      assert m.product([1, 2, 3, 4]) == 24
      assert m.product([]) == 1
    end

    test "count", %{m: m} do
      assert m.count([1, 2, 3, 4, 5], fn x -> x > 2 end) == 3
    end
  end

  # ============================================================================
  # Std.String
  # ============================================================================

  describe "Std.String" do
    setup do
      m = compile_stdlib("string")
      on_exit(fn -> purge(m) end)
      %{m: m}
    end

    test "length", %{m: m} do
      assert m.length("hello") == 5
      assert m.length("") == 0
    end

    test "is_empty", %{m: m} do
      assert m.is_empty("") == true
      assert m.is_empty("x") == false
    end

    test "concat", %{m: m} do
      assert m.concat("hello", " world") == "hello world"
    end

    test "from_int and from_atom", %{m: m} do
      assert m.from_int(42) == "42"
      assert m.from_atom(:hello) == "hello"
    end

    test "to_int", %{m: m} do
      assert m.to_int("42") == 42
    end

    test "to_atom", %{m: m} do
      assert m.to_atom("hello") == :hello
    end

    test "split", %{m: m} do
      assert m.split("a,b,c", ",") == ["a", "b,c"]
    end

    test "repeat", %{m: m} do
      assert m.repeat("ab", 3) == "ababab"
    end

    test "trim", %{m: m} do
      result = m.trim("  hello  ")
      assert is_binary(result) or is_list(result)
    end

    test "reverse", %{m: m} do
      assert m.reverse("hello") == "olleh"
      assert m.reverse("") == ""
    end
  end

  # ============================================================================
  # Std.Pair
  # ============================================================================

  describe "Std.Pair" do
    setup do
      m = compile_stdlib("pair")
      on_exit(fn -> purge(m) end)
      %{m: m}
    end

    test "first and second", %{m: m} do
      assert m.first({:a, :b}) == :a
      assert m.second({:a, :b}) == :b
    end

    test "swap", %{m: m} do
      assert m.swap({1, 2}) == {2, 1}
    end

    test "map_first", %{m: m} do
      assert m.map_first({5, :b}, fn x -> x * 2 end) == {10, :b}
    end

    test "map_second", %{m: m} do
      assert m.map_second({:a, 5}, fn x -> x * 2 end) == {:a, 10}
    end

    test "map_both", %{m: m} do
      result = m.map_both({1, 2}, fn x -> x * 10 end, fn x -> x * 100 end)
      assert result == {10, 200}
    end

    test "to_list", %{m: m} do
      assert [_, _] = m.to_list({:a, :b})
    end
  end

  # ============================================================================
  # Std.System
  # ============================================================================

  describe "Std.System" do
    setup do
      m = compile_stdlib("system")
      on_exit(fn -> purge(m) end)
      %{m: m}
    end

    test "timestamp_ms returns integer", %{m: m} do
      ts = m.timestamp_ms()
      assert is_integer(ts)
      assert ts > 0
    end

    test "self returns pid", %{m: m} do
      assert is_pid(m.self())
    end

    test "node returns atom", %{m: m} do
      assert is_atom(m.node())
    end

    test "cpu_count returns positive integer", %{m: m} do
      count = m.cpu_count()
      assert is_integer(count)
      assert count > 0
    end
  end

  # ============================================================================
  # Std.Access
  # ============================================================================

  describe "Std.Access -- factories" do
    setup do
      Cure.Stdlib.Preload.preload(examples: false)
      m = compile_stdlib("access")
      on_exit(fn -> purge(m) end)
      %{m: m}
    end

    test "key/1 returns AccKey ADT", %{m: m} do
      assert m.key(:name) == {:acc_key, :name}
    end

    test "key_default/2 returns AccKeyDefault ADT", %{m: m} do
      assert m.key_default(:name, "anon") == {:acc_key_default, :name, "anon"}
    end

    test "key_bang/1 returns AccKeyReq ADT", %{m: m} do
      assert m.key_bang(:name) == {:acc_key_req, :name}
    end

    test "elem_at/1 returns AccTupleElem ADT", %{m: m} do
      assert m.elem_at(2) == {:acc_tuple_elem, 2}
    end

    test "at/1 returns AccListAt ADT", %{m: m} do
      assert m.at(3) == {:acc_list_at, 3}
    end

    test "all/0 returns nullary AccListAll ADT", %{m: m} do
      assert m.all() == {:acc_list_all}
    end

    test "filter/1 returns AccListFilter ADT carrying the predicate", %{m: m} do
      pred = fn x -> x > 0 end
      assert {:acc_list_filter, ^pred} = m.filter(pred)
    end
  end

  describe "Std.Access -- Map impl (fetch/get/get_and_update/pop)" do
    setup do
      Cure.Stdlib.Preload.preload(examples: false)
      m = compile_stdlib("access")
      on_exit(fn -> purge(m) end)
      %{m: m}
    end

    test "fetch/2 returns Some(value) on hit and None() on miss", %{m: m} do
      assert m.fetch(%{a: 1, b: 2}, :a) == {:some, 1}
      assert m.fetch(%{a: 1}, :missing) == {:none}
    end

    test "fetch_bang/2 returns the value on hit", %{m: m} do
      assert m.fetch_bang(%{a: 1}, :a) == 1
    end

    test "fetch_bang/2 raises on miss", %{m: m} do
      assert_raise ErlangError, fn -> m.fetch_bang(%{a: 1}, :missing) end
    end

    test "get/3 returns the value or default", %{m: m} do
      assert m.get(%{a: 1}, :a, 0) == 1
      assert m.get(%{a: 1}, :missing, 0) == 0
    end

    test "get_and_update/3 updates an existing key", %{m: m} do
      result = m.get_and_update(%{a: 1}, :a, fn _opt -> {1, 42} end)
      assert result == {1, %{a: 42}}
    end

    test "get_and_update/3 inserts when the key is missing", %{m: m} do
      result = m.get_and_update(%{}, :new, fn _opt -> {nil, 99} end)
      assert result == {nil, %{new: 99}}
    end

    test "get_and_update/3 :pop removes the key", %{m: m} do
      result = m.get_and_update(%{a: 1, b: 2}, :a, fn _opt -> :pop end)
      assert result == {1, %{b: 2}}
    end

    test "get_and_update/3 :pop on missing key leaves the map untouched", %{m: m} do
      result = m.get_and_update(%{b: 2}, :a, fn _opt -> :pop end)
      assert result == {nil, %{b: 2}}
    end

    test "pop/2 returns {value, without_key}", %{m: m} do
      assert m.pop(%{a: 1, b: 2}, :a) == {1, %{b: 2}}
      assert m.pop(%{b: 2}, :missing) == {nil, %{b: 2}}
    end

    test "pop/2 on a struct-like map (with :__struct__) raises", %{m: m} do
      struct_like = %{__struct__: :person, name: "Alice"}
      assert_raise ErlangError, fn -> m.pop(struct_like, :name) end
    end
  end

  describe "Std.Access -- List (keyword) impl" do
    setup do
      Cure.Stdlib.Preload.preload(examples: false)
      m = compile_stdlib("access")
      on_exit(fn -> purge(m) end)
      %{m: m}
    end

    test "fetch/2 walks a keyword-shaped list", %{m: m} do
      kw = [{:a, 1}, {:b, 2}]
      assert m.fetch(kw, :a) == {:some, 1}
      assert m.fetch(kw, :b) == {:some, 2}
      assert m.fetch(kw, :missing) == {:none}
    end

    test "get_and_update/3 replaces the first matching pair", %{m: m} do
      result = m.get_and_update([{:a, 1}, {:b, 2}], :a, fn _opt -> {1, 10} end)
      assert result == {1, [{:a, 10}, {:b, 2}]}
    end

    test "get_and_update/3 appends when the key is missing", %{m: m} do
      result = m.get_and_update([{:a, 1}], :b, fn _opt -> {nil, 2} end)
      assert result == {nil, [{:a, 1}, {:b, 2}]}
    end

    test "get_and_update/3 :pop removes the pair", %{m: m} do
      result = m.get_and_update([{:a, 1}, {:b, 2}], :a, fn _opt -> :pop end)
      assert result == {1, [{:b, 2}]}
    end

    test "pop/2 returns the popped value and the rest", %{m: m} do
      assert m.pop([{:a, 1}, {:b, 2}], :b) == {2, [{:a, 1}]}
      assert m.pop([{:a, 1}], :missing) == {nil, [{:a, 1}]}
    end
  end

  describe "Std.Access -- nested helpers on maps" do
    setup do
      Cure.Stdlib.Preload.preload(examples: false)
      m = compile_stdlib("access")
      on_exit(fn -> purge(m) end)
      %{m: m}
    end

    test "fetch_in/2 through nested maps", %{m: m} do
      data = %{user: %{name: "Alice", age: 30}}
      assert m.fetch_in(data, [m.key(:user), m.key(:name)]) == {:some, "Alice"}
      assert m.fetch_in(data, [m.key(:user), m.key(:missing)]) == {:none}
    end

    test "get_in/2 returns nil for missing intermediate keys", %{m: m} do
      data = %{user: %{name: "Alice"}}
      assert m.get_in(data, [m.key(:user), m.key(:name)]) == "Alice"
      assert m.get_in(data, [m.key(:user), m.key(:age)]) == nil
      assert m.get_in(data, [m.key(:missing), m.key(:age)]) == nil
    end

    test "put_in/3 rebuilds nested maps", %{m: m} do
      data = %{user: %{name: "Alice", age: 30}}
      updated = m.put_in(data, [m.key(:user), m.key(:age)], 31)
      assert updated == %{user: %{name: "Alice", age: 31}}
    end

    test "update_in/3 applies a function at the leaf", %{m: m} do
      data = %{user: %{age: 30}}
      updated = m.update_in(data, [m.key(:user), m.key(:age)], fn age -> age + 1 end)
      assert updated == %{user: %{age: 31}}
    end

    test "pop_in/2 removes a nested key", %{m: m} do
      data = %{user: %{name: "Alice", age: 30}}
      {popped, rebuilt} = m.pop_in(data, [m.key(:user), m.key(:age)])
      assert popped == 30
      assert rebuilt == %{user: %{name: "Alice"}}
    end

    test "get_and_update_in/3 can both read and write", %{m: m} do
      data = %{user: %{age: 30}}

      {old, new_data} =
        m.get_and_update_in(data, [m.key(:user), m.key(:age)], fn age ->
          {age, age * 2}
        end)

      assert old == 30
      assert new_data == %{user: %{age: 60}}
    end
  end

  describe "Std.Access -- lens-style accessors (all/filter/at/elem_at)" do
    setup do
      Cure.Stdlib.Preload.preload(examples: false)
      m = compile_stdlib("access")
      on_exit(fn -> purge(m) end)
      %{m: m}
    end

    test "all/0 traverses every element of a list", %{m: m} do
      data = %{
        langs: [
          %{name: "elixir"},
          %{name: "cure"}
        ]
      }

      names = m.get_in(data, [m.key(:langs), m.all(), m.key(:name)])
      assert names == ["elixir", "cure"]
    end

    test "update_in with all/0 upcases every nested name", %{m: m} do
      data = %{
        langs: [
          %{name: "elixir"},
          %{name: "cure"}
        ]
      }

      updated =
        m.update_in(data, [m.key(:langs), m.all(), m.key(:name)], fn name ->
          String.upcase(name)
        end)

      assert updated == %{langs: [%{name: "ELIXIR"}, %{name: "CURE"}]}
    end

    test "filter/1 only touches elements satisfying the predicate", %{m: m} do
      data = [%{n: 1}, %{n: 2}, %{n: 3}]
      pick_even = m.filter(fn item -> rem(Map.get(item, :n), 2) == 0 end)

      updated = m.update_in(data, [pick_even, m.key(:n)], fn n -> n * 10 end)
      assert updated == [%{n: 1}, %{n: 20}, %{n: 3}]
    end

    test "at/1 updates a specific list index", %{m: m} do
      data = [10, 20, 30]
      updated = m.update_in(data, [m.at(1)], fn x -> x * 2 end)
      assert updated == [10, 40, 30]
    end

    test "elem_at/1 reads and updates a tuple element (0-based)", %{m: m} do
      data = {:a, :b, :c}
      assert m.get_in(data, [m.elem_at(1)]) == :b
      assert m.update_in(data, [m.elem_at(1)], fn _ -> :x end) == {:a, :x, :c}
    end

    test "key_bang/1 raises on a missing intermediate key", %{m: m} do
      data = %{user: %{name: "Alice"}}

      assert_raise ErlangError, fn ->
        m.get_in(data, [m.key(:user), m.key_bang(:missing)])
      end
    end
  end
end
