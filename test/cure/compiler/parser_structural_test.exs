defmodule Cure.Compiler.ParserStructuralTest do
  use ExUnit.Case, async: true

  alias Cure.Compiler.{Lexer, Parser}

  defp parse!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  # ── Named Function Definitions ───────────────────────────────────────

  describe "named function definitions" do
    test "simple fn with typed params and return type" do
      ast = parse!("fn add(x: Int, y: Int) -> Int = x + y")
      assert {:function_def, meta, [_body]} = ast
      assert meta[:name] == "add"
      assert meta[:visibility] == :public
      assert meta[:arity] == 2
      assert meta[:return_type] != nil
      assert [_, _] = meta[:params]
    end

    test "fn params have type annotations" do
      ast = parse!("fn inc(n: Int) -> Int = n + 1")
      assert {:function_def, meta, _} = ast
      [{:param, param_meta, "n"}] = meta[:params]
      assert param_meta[:type] != nil
    end

    test "private function with local keyword" do
      ast = parse!("local fn helper(x: Int) -> Int = x + 1")
      assert {:function_def, meta, _} = ast
      assert meta[:visibility] == :private
    end

    test "fn with when guard" do
      ast = parse!("fn abs(x: Int) -> Int when x >= 0 = x")
      assert {:function_def, meta, _} = ast
      assert meta[:guards] != nil
    end

    test "fn with where constraints" do
      ast = parse!("fn sort(xs: List) -> List where Ord(T) = xs")
      assert {:function_def, meta, _} = ast
      assert [_] = meta[:constraints]
    end

    test "fn signature only (no body, for protocols)" do
      ast = parse!("fn show(x: T) -> String")
      assert {:function_def, meta, []} = ast
      assert meta[:name] == "show"
    end

    test "fn with default parameter" do
      ast = parse!(~s[fn greet(name: String, greeting: String = "Hello") -> String = name])
      assert {:function_def, meta, _} = ast
      params = meta[:params]
      assert [_, {:param, p2_meta, "greeting"}] = params
      assert p2_meta[:default] != nil
    end

    test "multi-clause function with | patterns" do
      source = "fn factorial(n: Nat) -> Nat\n  | 0 -> 1\n  | n -> n"
      ast = parse!(source)
      assert {:function_def, meta, []} = ast
      assert meta[:name] == "factorial"
      clauses = meta[:clauses]
      assert [_, _] = clauses
    end
  end

  # ── Modules ──────────────────────────────────────────────────────────

  describe "modules" do
    test "simple module with function" do
      source = "mod MyApp\n  fn hello() -> String = \"hi\""
      ast = parse!(source)
      assert {:container, meta, body} = ast
      assert meta[:container_type] == :module
      assert meta[:name] == "MyApp"
      assert [_fn_def] = body
    end

    test "module with dotted name" do
      source = "mod MyApp.Users\n  fn create() -> Int = 1"
      ast = parse!(source)
      assert {:container, meta, _} = ast
      assert meta[:name] == "MyApp.Users"
    end
  end

  # ── Records ──────────────────────────────────────────────────────────

  describe "records" do
    test "simple record with fields" do
      source = "rec Person\n  name: String\n  age: Int"
      ast = parse!(source)
      assert {:container, meta, fields} = ast
      assert meta[:container_type] == :struct
      assert meta[:name] == "Person"
      assert [_, _] = fields
    end

    test "record field has type" do
      source = "rec Point\n  x: Float\n  y: Float"
      ast = parse!(source)
      assert {:container, _, [{:param, field_meta, "x"} | _]} = ast
      assert field_meta[:type] != nil
    end

    test "record with type parameters" do
      source = "rec Pair(A, B)\n  first: A\n  second: B"
      ast = parse!(source)
      assert {:container, meta, _} = ast
      assert meta[:type_params] == ["A", "B"]
    end
  end

  # ── Type Definitions ─────────────────────────────────────────────────

  describe "type definitions" do
    test "ADT with constructors" do
      ast = parse!("type Option(T) = Some(T) | None")
      assert {:container, meta, variants} = ast
      assert meta[:container_type] == :enum
      assert meta[:name] == "Option"
      assert meta[:type_params] == ["T"]
      assert [_, _] = variants
    end

    test "ADT constructor has params" do
      ast = parse!("type Result(T, E) = Ok(T) | Error(E)")
      assert {:container, _, [ok, err]} = ast
      assert {:function_def, ok_meta, []} = ok
      assert ok_meta[:name] == "Ok"
      assert ok_meta[:variant] == true
      assert {:function_def, err_meta, []} = err
      assert err_meta[:name] == "Error"
    end

    test "nullary constructor" do
      ast = parse!("type Color = Red | Green | Blue")
      assert {:container, _, [r, g, b]} = ast
      assert {:variable, r_meta, "Red"} = r
      assert r_meta[:variant] == true
      assert {:variable, _, "Green"} = g
      assert {:variable, _, "Blue"} = b
    end

    test "type alias" do
      ast = parse!("type Name = String")
      assert {:type_annotation, meta, [_type_expr]} = ast
      assert meta[:name] == "Name"
    end

    test "refinement type" do
      ast = parse!("type Nat = {x: Int | x >= 0}")
      assert {:type_annotation, meta, [_var, _base, _pred]} = ast
      assert meta[:name] == "Nat"
      assert meta[:refinement] == true
    end
  end

  # ── Protocols ────────────────────────────────────────────────────────

  describe "protocols" do
    test "protocol with method signature" do
      source = "proto Show(T)\n  fn show(x: T) -> String"
      ast = parse!(source)
      assert {:container, meta, body} = ast
      assert meta[:container_type] == :protocol
      assert meta[:name] == "Show"
      assert meta[:type_params] == ["T"]
      assert [_fn_sig] = body
    end
  end

  # ── Implementations ─────────────────────────────────────────────────

  describe "implementations" do
    test "simple impl" do
      source = "impl Show for Int\n  fn show(x: Int) -> String = x"
      ast = parse!(source)
      assert {:container, meta, body} = ast
      assert meta[:container_type] == :trait
      assert meta[:protocol] == "Show"
      assert meta[:for] == "Int"
      assert [_fn_def] = body
    end
  end

  # ── Imports ──────────────────────────────────────────────────────────

  describe "imports" do
    test "import all from module" do
      ast = parse!("use Std.List")
      assert {:import, meta, []} = ast
      assert meta[:source] == "Std.List"
      assert meta[:import_type] == :use
    end

    test "selective import" do
      ast = parse!("use Std.List.{map, filter}")
      assert {:import, meta, []} = ast
      assert meta[:source] == "Std.List"
      assert meta[:items] == ["map", "filter"]
    end

    test "aliased import" do
      ast = parse!("use Std.Io as IO")
      assert {:import, meta, []} = ast
      assert meta[:source] == "Std.Io"
      assert meta[:alias] == "IO"
    end
  end

  # ── Decorator Attachment ────────────────────────────────────────────

  describe "decorator attachment" do
    test "@doc attaches to fn" do
      source = "@doc(\"Adds two numbers\")\nfn add(x: Int, y: Int) -> Int = x + y"
      ast = parse!(source)
      assert {:function_def, meta, _} = ast
      assert meta[:decorator] != nil
    end

    test "@extern attaches as FFI metadata" do
      source = "@extern(:io, :format, 2)\nfn print_raw(format: String, args: List) -> Unit"
      ast = parse!(source)
      assert {:function_def, meta, _} = ast
      assert {:io, :format, 2} = meta[:extern]
    end
  end

  # ── FSM Definitions ─────────────────────────────────────────────────

  describe "FSM definitions" do
    test "simple FSM with transitions" do
      source =
        "fsm TrafficLight with TrafficPayload{}\n  Red --timer--> Green\n  Green --timer--> Yellow\n  Yellow --timer--> Red"

      ast = parse!(source)
      assert {:container, meta, transitions} = ast
      assert meta[:container_type] == :fsm
      assert meta[:name] == "TrafficLight"
      assert [_, _, _] = transitions
    end

    test "FSM transition has from/event/to metadata" do
      source = "fsm Counter with Payload{}\n  Idle --start--> Running"
      ast = parse!(source)
      assert {:container, _, [t]} = ast
      assert {:function_call, t_meta, []} = t
      assert t_meta[:from] == "Idle"
      assert t_meta[:event] == "start"
      assert t_meta[:to] == "Running"
    end

    test "FSM with guarded transition" do
      source = "fsm Counter with Payload{}\n  Counting --increment when value < 100--> Counting"
      ast = parse!(source)
      assert {:container, _, [t]} = ast
      assert {:function_call, t_meta, []} = t
      assert t_meta[:guard] != nil
    end
  end

  # ── Enhanced Type Expressions ───────────────────────────────────────

  describe "type expressions" do
    test "parameterized type" do
      ast = parse!("fn id(x: List(Int)) -> List(Int) = x")
      assert {:function_def, meta, _} = ast
      [{:param, pm, _}] = meta[:params]
      assert {:function_call, tmeta, _} = pm[:type]
      assert tmeta[:name] == "List"
    end
  end

  # ── Lambdas Still Work ─────────────────────────────────────────────

  describe "lambda (Milestone 2 regression)" do
    test "anonymous fn still works" do
      ast = parse!("fn(x) -> x + 1")
      assert {:lambda, _, _} = ast
    end
  end
end
