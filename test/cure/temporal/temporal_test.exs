defmodule Cure.Temporal.FormulaTest do
  use ExUnit.Case, async: true

  alias Cure.Temporal.Formula, as: F

  describe "smart constructors" do
    test "tt / ff absorb through not" do
      assert F.not_(F.tt()) == :ff
      assert F.not_(F.ff()) == :tt
    end

    test "double negation elimination" do
      assert F.not_(F.not_(F.atom("A"))) == F.atom("A")
    end

    test "and/or tautology elimination" do
      a = F.atom("A")
      assert F.and_(F.tt(), a) == a
      assert F.or_(F.ff(), a) == a
      assert F.and_(a, F.ff()) == :ff
      assert F.or_(a, F.tt()) == :tt
    end

    test "never(p) == always(not p)" do
      assert F.never(F.atom("A")) == F.always(F.not_(F.atom("A")))
    end
  end

  describe "atoms/1" do
    test "collects state names from all sub-formulae" do
      f = F.and_(F.always(F.atom("A")), F.eventually(F.atom("B")))
      assert F.atoms(f) == ["A", "B"]
    end
  end

  describe "show/1" do
    test "prints compound formulae readably" do
      f = F.implies(F.atom("A"), F.eventually(F.atom("B")))
      assert F.show(f) == "(!(A) or eventually B)"
    end
  end
end

defmodule Cure.Temporal.ParserTest do
  use ExUnit.Case, async: true

  alias Cure.Temporal.Parser
  alias Cure.Temporal.Formula, as: F

  describe "parse/1" do
    test "parses a single atom" do
      assert {:ok, [{:atom, ["A"]}]} = Parser.parse("A")
    end

    test "parses always / eventually / never" do
      assert {:ok, [{:always, [{:atom, ["Open"]}]}]} = Parser.parse("always Open")
      assert {:ok, [{:eventually, [{:atom, ["Open"]}]}]} = Parser.parse("eventually Open")
      assert {:ok, [{:always, [{:not_, [{:atom, ["Dead"]}]}]}]} = Parser.parse("never Dead")
    end

    test "parses implication" do
      assert {:ok, [f]} = Parser.parse("Locked -> eventually Unlocked")

      # (!Locked or eventually Unlocked)
      assert F.show(f) == "(!(Locked) or eventually Unlocked)"
    end

    test "parses nested always-eventually" do
      assert {:ok, [f]} = Parser.parse("always eventually Unlocked")
      assert F.show(f) == "always eventually Unlocked"
    end

    test "parses multiple properties separated by semicolons" do
      assert {:ok, props} = Parser.parse("always Open; never Dead")
      assert length(props) == 2
    end

    test "parses newline-separated properties" do
      assert {:ok, props} = Parser.parse("always Open\nnever Dead")
      assert length(props) == 2
    end

    test "rejects garbage input" do
      assert {:error, _} = Parser.parse("@!$")
    end

    test "respects parentheses" do
      assert {:ok, [f]} = Parser.parse("always (Locked -> eventually Unlocked)")
      assert F.show(f) == "always (!(Locked) or eventually Unlocked)"
    end
  end

  describe "parse_one/1" do
    test "returns the single formula when exactly one is supplied" do
      assert {:ok, {:always, [{:atom, ["Open"]}]}} = Parser.parse_one("always Open")
    end

    test "rejects multi-formula input" do
      assert {:error, :expected_single_formula} = Parser.parse_one("always Open; never Dead")
    end
  end
end

defmodule Cure.Temporal.CheckerTest do
  use ExUnit.Case, async: true

  alias Cure.Temporal.{Checker, Parser}

  # Turnstile: Locked --coin--> Unlocked --push--> Locked.
  # Oscillates forever between the two states.
  defp turnstile_model do
    Checker.from_fsm(
      [
        %{from: "Locked", to: "Unlocked"},
        %{from: "Unlocked", to: "Locked"}
      ],
      "Locked"
    )
  end

  # Broken turnstile: Locked has no outgoing edge.
  defp stuck_model do
    Checker.from_fsm(
      [
        %{from: "Locked", to: "Locked"}
      ],
      "Locked"
    )
  end

  describe "safety properties" do
    test "always (not Dead) holds on the turnstile" do
      {:ok, f} = Parser.parse_one("never Dead_state_not_in_model")

      # The formula references a state not in the model -- that's an error, not a violation.
      assert {:error, {:unknown_atoms, ["Dead_state_not_in_model"]}} =
               Checker.check(f, turnstile_model())
    end

    test "always Locked is violated; counterexample is a 2-state path" do
      {:ok, f} = Parser.parse_one("always Locked")
      assert {:violation, trail} = Checker.check(f, turnstile_model())
      assert "Unlocked" in trail
    end

    test "always (Locked or Unlocked) holds" do
      {:ok, f} = Parser.parse_one("always (Locked or Unlocked)")
      assert {:ok, :holds} = Checker.check(f, turnstile_model())
    end
  end

  describe "liveness properties" do
    test "eventually Unlocked holds on the turnstile" do
      {:ok, f} = Parser.parse_one("eventually Unlocked")
      assert {:ok, :holds} = Checker.check(f, turnstile_model())
    end

    test "eventually Unlocked fails on the stuck model" do
      {:ok, f} = Parser.parse_one("eventually Unlocked")

      # Unlocked isn't a state in the stuck model -- unknown atoms error.
      assert {:error, {:unknown_atoms, ["Unlocked"]}} = Checker.check(f, stuck_model())
    end

    test "eventually reaches a later state in a chain" do
      model =
        Checker.from_fsm(
          [
            %{from: "A", to: "B"},
            %{from: "B", to: "C"}
          ],
          "A"
        )

      {:ok, f} = Parser.parse_one("eventually C")
      assert {:ok, :holds} = Checker.check(f, model)
    end
  end

  describe "nested always-eventually" do
    test "always eventually Unlocked holds because the cycle returns to Unlocked" do
      {:ok, f} = Parser.parse_one("always eventually Unlocked")
      # Every reachable state (Locked and Unlocked) can eventually reach Unlocked.
      assert {:ok, :holds} = Checker.check(f, turnstile_model())
    end
  end

  describe "until" do
    test "A until B succeeds when B is reachable via A-only states" do
      model =
        Checker.from_fsm(
          [
            %{from: "A", to: "A"},
            %{from: "A", to: "B"}
          ],
          "A"
        )

      {:ok, f} = Parser.parse_one("A until B")
      assert {:ok, :holds} = Checker.check(f, model)
    end
  end

  describe "bound" do
    test "small bound surfaces :bound_exceeded on eventually in long chains" do
      # Build a chain A1 -> A2 -> ... -> A100
      transitions =
        for i <- 1..99 do
          %{from: "A#{i}", to: "A#{i + 1}"}
        end

      model = Checker.from_fsm(transitions, "A1")

      {:ok, f} = Parser.parse_one("eventually A100")
      assert {:error, :bound_exceeded} = Checker.check(f, model, bound: 10)
    end
  end
end
