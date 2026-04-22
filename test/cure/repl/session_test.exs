defmodule Cure.REPL.SessionTest do
  # async: false -- compile/1 loads a global BEAM module (`:"Cure.Repl.Session"`)
  # into the VM; running in parallel would clobber sibling tests.
  use ExUnit.Case, async: false

  alias Cure.REPL.Session

  setup do
    Session.clear()
    on_exit(&Session.clear/0)
    :ok
  end

  describe "classify/1" do
    test "named function definition" do
      assert {:definitions, [entry]} =
               Session.classify("fn add(a: Int, b: Int) -> Int = a + b")

      assert entry.kind == :fn
      assert entry.key == {:fn, "add", 2, :public}
      assert entry.label == "add/2"
      assert entry.source == "fn add(a: Int, b: Int) -> Int = a + b"
    end

    test "local (private) function definition" do
      assert {:definitions, [entry]} =
               Session.classify("local fn helper(x: Int) -> Int = x + 1")

      assert entry.kind == :fn
      assert entry.key == {:fn, "helper", 1, :private}
      assert entry.label == "helper/1"
    end

    test "nullary function" do
      assert {:definitions, [entry]} =
               Session.classify("fn pi() -> Float = 3.14")

      assert entry.key == {:fn, "pi", 0, :public}
      assert entry.label == "pi/0"
    end

    test "multi-line function with indented body" do
      src = """
      fn clamp(x: Int, lo: Int, hi: Int) -> Int =
        if x < lo then lo
        else if x > hi then hi
        else x
      """

      assert {:definitions, [entry]} = Session.classify(src)
      assert entry.key == {:fn, "clamp", 3, :public}
    end

    test "ADT type declaration" do
      assert {:definitions, [entry]} =
               Session.classify("type Color = Red | Green | Blue")

      assert entry.kind == :type
      assert entry.key == {:type, "Color"}
      assert entry.label == "type Color"
    end

    test "parameterised ADT" do
      assert {:definitions, [entry]} =
               Session.classify("type Option(T) = Some(T) | None")

      assert entry.kind == :type
      assert entry.key == {:type, "Option"}
    end

    test "record declaration" do
      src = """
      rec Point
        x: Int
        y: Int
      """

      assert {:definitions, [entry]} = Session.classify(src)
      assert entry.kind == :rec
      assert entry.key == {:rec, "Point"}
      assert entry.label == "rec Point"
    end

    test "lambda is an expression, not a definition" do
      assert :expression = Session.classify("fn(x) -> x + 1 end")
    end

    test "bare expression" do
      assert :expression = Session.classify("1 + 2")
      assert :expression = Session.classify("foo(1, 2, 3)")
      assert :expression = Session.classify("[1, 2, 3]")
    end

    test "multiple declarations in one submission" do
      src = """
      fn inc(x: Int) -> Int = x + 1
      fn dec(x: Int) -> Int = x - 1
      """

      assert {:definitions, [inc, dec]} = Session.classify(src)
      assert inc.key == {:fn, "inc", 1, :public}
      assert dec.key == {:fn, "dec", 1, :public}
    end

    test "declaration followed by expression falls back to expression" do
      src = """
      fn inc(x: Int) -> Int = x + 1
      inc(1)
      """

      assert :expression = Session.classify(src)
    end

    test "parse error falls back to expression" do
      # Deliberately malformed: lets the compiler's normal diagnostics
      # kick in via the expression path.
      assert :expression = Session.classify("fn ??? garbage")
    end

    test "empty input" do
      assert :expression = Session.classify("")
      assert :expression = Session.classify("   \n\n  ")
    end
  end

  describe "merge/2" do
    test "new entries append in insertion order" do
      [e1, e2] =
        [
          %{key: {:fn, "a", 0, :public}, kind: :fn, label: "a/0", source: "fn a() -> Int = 1"},
          %{key: {:fn, "b", 0, :public}, kind: :fn, label: "b/0", source: "fn b() -> Int = 2"}
        ]

      {defs, events} = Session.merge([], [e1, e2])

      assert [^e1, ^e2] = defs
      assert [{:new, ^e1}, {:new, ^e2}] = events
    end

    test "redefined entry replaces in place and tags :redefined" do
      e1 = %{key: {:fn, "a", 0, :public}, kind: :fn, label: "a/0", source: "fn a() -> Int = 1"}
      e2 = %{key: {:fn, "b", 0, :public}, kind: :fn, label: "b/0", source: "fn b() -> Int = 2"}

      e1_v2 = %{e1 | source: "fn a() -> Int = 42"}

      {defs, events} = Session.merge([e1, e2], [e1_v2])

      assert [^e1_v2, ^e2] = defs
      assert [{:redefined, ^e1_v2}] = events
    end

    test "different arities coexist" do
      a1 = %{key: {:fn, "f", 1, :public}, kind: :fn, label: "f/1", source: "fn f(x: Int) -> Int = x"}

      a2 = %{
        key: {:fn, "f", 2, :public},
        kind: :fn,
        label: "f/2",
        source: "fn f(x: Int, y: Int) -> Int = x + y"
      }

      {defs, _} = Session.merge([a1], [a2])
      assert [^a1, ^a2] = defs
    end
  end

  describe "build_source/1" do
    test "empty defs produce the empty string" do
      assert "" = Session.build_source([])
    end

    test "wraps entries in mod Repl.Session" do
      entry = %{
        key: {:fn, "one", 0, :public},
        kind: :fn,
        label: "one/0",
        source: "fn one() -> Int = 1"
      }

      src = Session.build_source([entry])
      assert String.starts_with?(src, "mod Repl.Session\n")
      assert String.contains?(src, "  fn one() -> Int = 1")
    end
  end

  describe "compile/1 + clear/0" do
    test "compiles a single function and loads the module" do
      entry = %{
        key: {:fn, "double", 1, :public},
        kind: :fn,
        label: "double/1",
        source: "fn double(x: Int) -> Int = x * 2"
      }

      assert {:ok, module} = Session.compile([entry])
      assert module == Session.module_atom()
      assert 42 = module.double(21)
    end

    test "recompilation replaces the loaded module in place" do
      e_v1 = %{
        key: {:fn, "answer", 0, :public},
        kind: :fn,
        label: "answer/0",
        source: "fn answer() -> Int = 1"
      }

      e_v2 = %{e_v1 | source: "fn answer() -> Int = 42"}

      assert {:ok, mod} = Session.compile([e_v1])
      assert 1 = mod.answer()

      assert {:ok, ^mod} = Session.compile([e_v2])
      assert 42 = mod.answer()
    end

    test "empty defs returns :empty and unloads a previously-loaded module" do
      entry = %{
        key: {:fn, "gone", 0, :public},
        kind: :fn,
        label: "gone/0",
        source: "fn gone() -> Int = 0"
      }

      assert {:ok, _} = Session.compile([entry])
      assert :empty = Session.compile([])
      refute :code.is_loaded(Session.module_atom())
    end
  end

  describe "signatures/1" do
    test "empty input yields an empty list" do
      assert [] = Session.signatures([])
    end

    test "public fn entry yields a resolved {:fun, params, ret} signature" do
      entry = %{
        key: {:fn, "add", 2, :public},
        kind: :fn,
        label: "add/2",
        source: "fn add(a: Int, b: Int) -> Int = a + b"
      }

      assert [{"add", {:fun, [:int, :int], :int}}] = Session.signatures([entry])
    end

    test "missing return type falls back to :any" do
      entry = %{
        key: {:fn, "untyped", 1, :public},
        kind: :fn,
        label: "untyped/1",
        source: "fn untyped(x) = x"
      }

      assert [{"untyped", {:fun, [:any], :any}}] = Session.signatures([entry])
    end

    test "private (local) fns are not exposed" do
      entry = %{
        key: {:fn, "hidden", 0, :private},
        kind: :fn,
        label: "hidden/0",
        source: "local fn hidden() -> Int = 1"
      }

      assert [] = Session.signatures([entry])
    end

    test "non-fn entries are ignored" do
      rec = %{key: {:rec, "Point"}, kind: :rec, label: "rec Point", source: "rec Point\n  x: Int"}
      type = %{key: {:type, "Color"}, kind: :type, label: "type Color", source: "type Color = Red"}

      assert [] = Session.signatures([rec, type])
    end
  end
end
