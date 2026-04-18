defmodule Cure.FSM.FSMCallbackTest do
  use ExUnit.Case, async: false

  alias Cure.FSM.{Verifier, Compiler}
  alias Cure.Compiler.BeamWriter

  # ============================================================================
  # Event Kind (!/?) Tests -- Simple mode (gen_statem)
  # ============================================================================

  describe "event kind in simple mode" do
    test "normal events have event_kind: :normal in transitions table" do
      ast = traffic_light_ast()
      {:ok, forms} = Compiler.compile(ast, emit_events: false)
      {:ok, mod} = BeamWriter.compile_and_load(forms)

      table = mod.transitions()
      assert [_, _, _] = table
      assert Enum.all?(table, fn {_f, _e, _t, kind} -> kind == :normal end)

      GenServer.stop(elem(mod.start_link(), 1))
    after
      purge(:"Cure.FSM.TrafficNormal")
    end

    test "soft events silently keep state on unmatched transitions" do
      ast = soft_event_ast()
      {:ok, forms} = Compiler.compile(ast, emit_events: false)
      {:ok, mod} = BeamWriter.compile_and_load(forms)

      {:ok, pid} = mod.start_link()

      # Initial state: active
      {state, _} = mod.get_state(pid)
      assert state == :active

      # poll is a soft event -- should transition active -> active
      mod.send_event(pid, :poll)
      _ = :sys.get_state(pid)
      {state, _} = mod.get_state(pid)
      assert state == :active

      # done transitions to finished
      mod.send_event(pid, :done)
      _ = :sys.get_state(pid)
      {state, _} = mod.get_state(pid)
      assert state == :finished

      # poll from finished -- no transition, soft event, stays in finished
      mod.send_event(pid, :poll)
      _ = :sys.get_state(pid)
      {state, _} = mod.get_state(pid)
      assert state == :finished

      GenServer.stop(pid)
    after
      purge(:"Cure.FSM.SoftTest")
    end

    test "hard events auto-fire via next_event action" do
      ast = hard_event_ast()
      {:ok, forms} = Compiler.compile(ast, emit_events: false)
      {:ok, mod} = BeamWriter.compile_and_load(forms)

      {:ok, pid} = mod.start_link()
      {state, _} = mod.get_state(pid)
      assert state == :idle

      # trigger! fires from idle -> setup, and setup has auto! which auto-fires to ready
      mod.send_event(pid, :trigger)
      _ = :sys.get_state(pid)
      Process.sleep(10)
      {state, _} = mod.get_state(pid)
      # Should have auto-advanced through setup -> ready
      assert state == :ready

      GenServer.stop(pid)
    after
      purge(:"Cure.FSM.HardTest")
    end

    test "allowed/2 returns true for valid transitions" do
      ast = traffic_light_ast()
      {:ok, forms} = Compiler.compile(ast, emit_events: false)
      {:ok, mod} = BeamWriter.compile_and_load(forms)

      assert mod.allowed(:red, :timer) == true
      assert mod.allowed(:red, :emergency) == false
      assert mod.allowed(:green, :timer) == true
    after
      purge(:"Cure.FSM.TrafficNormal")
    end
  end

  # ============================================================================
  # Callback Mode Tests -- GenServer with on_transition
  # ============================================================================

  describe "callback mode (on_transition)" do
    test "compiles and runs a basic callback-mode FSM" do
      ast = callback_turnstile_ast()
      {:ok, {:callback_mode, mod}} = Compiler.compile(ast, emit_events: false)

      assert mod == :"Cure.FSM.CallbackTurnstile"
      {:ok, pid} = mod.start_link(0)

      # Initial state
      {state, data} = mod.get_state(pid)
      assert state == :locked
      assert data == 0

      # Insert coin
      mod.send_event(pid, :coin)
      Process.sleep(10)
      {state, data} = mod.get_state(pid)
      assert state == :unlocked
      assert data == 1

      # Push through
      mod.send_event(pid, :push)
      Process.sleep(10)
      {state, data} = mod.get_state(pid)
      assert state == :locked
      assert data == 1

      # Insert another coin
      mod.send_event(pid, :coin)
      Process.sleep(10)
      {state, data} = mod.get_state(pid)
      assert state == :unlocked
      assert data == 2

      GenServer.stop(pid)
    after
      purge(:"Cure.FSM.CallbackTurnstile")
    end

    test "transitions/0 returns the transition table" do
      ast = callback_turnstile_ast()
      {:ok, {:callback_mode, mod}} = Compiler.compile(ast, emit_events: false)
      assert mod == :"Cure.FSM.CallbackTurnstile"

      table = mod.transitions()
      assert [_, _, _, _] = table
      assert Enum.any?(table, fn {from, ev, to, _k} -> from == :locked and ev == :coin and to == :unlocked end)
    after
      purge(:"Cure.FSM.CallbackTurnstile")
    end

    test "responds?/2 checks event availability" do
      ast = callback_turnstile_ast()
      {:ok, {:callback_mode, mod}} = Compiler.compile(ast, emit_events: false)
      assert mod == :"Cure.FSM.CallbackTurnstile"

      assert mod.responds?(:locked, :coin) == true
      assert mod.responds?(:locked, :push) == true
      assert mod.responds?(:locked, :nonexistent) == false
    after
      purge(:"Cure.FSM.CallbackTurnstile")
    end
  end

  # ============================================================================
  # Verifier Tests
  # ============================================================================

  describe "verifier - hard event validation" do
    test "hard event as sole outgoing event passes" do
      ast = hard_event_ast()
      assert {:ok, _} = Verifier.verify(ast, emit_events: false)
    end

    test "hard event with other outgoing events fails" do
      ast = bad_hard_event_ast()
      assert {:error, errors} = Verifier.verify(ast, emit_events: false)
      assert Enum.any?(errors, fn {type, _, _} -> type == :hard_event_not_sole end)
    end
  end

  # ============================================================================
  # AST Helpers
  # ============================================================================

  defp traffic_light_ast do
    {:container, [container_type: :fsm, name: "TrafficNormal", line: 1],
     [
       {:function_call, [name: "transition", from: "Red", event: "timer", to: "Green", event_kind: :normal], []},
       {:function_call, [name: "transition", from: "Green", event: "timer", to: "Yellow", event_kind: :normal], []},
       {:function_call, [name: "transition", from: "Yellow", event: "timer", to: "Red", event_kind: :normal], []}
     ]}
  end

  defp soft_event_ast do
    {:container, [container_type: :fsm, name: "SoftTest", line: 1],
     [
       {:function_call, [name: "transition", from: "Active", event: "poll", to: "Active", event_kind: :soft], []},
       {:function_call, [name: "transition", from: "Active", event: "done", to: "Finished", event_kind: :normal], []}
     ]}
  end

  defp hard_event_ast do
    {:container, [container_type: :fsm, name: "HardTest", line: 1],
     [
       {:function_call, [name: "transition", from: "Idle", event: "trigger", to: "Setup", event_kind: :normal], []},
       {:function_call, [name: "transition", from: "Setup", event: "auto", to: "Ready", event_kind: :hard], []},
       {:function_call, [name: "transition", from: "Ready", event: "process", to: "Idle", event_kind: :normal], []}
     ]}
  end

  defp bad_hard_event_ast do
    # Hard event "go" from A, but A also has normal event "stay"
    {:container, [container_type: :fsm, name: "BadHard", line: 1],
     [
       {:function_call, [name: "transition", from: "A", event: "go", to: "B", event_kind: :hard], []},
       {:function_call, [name: "transition", from: "A", event: "stay", to: "A", event_kind: :normal], []},
       {:function_call, [name: "transition", from: "B", event: "back", to: "A", event_kind: :normal], []}
     ]}
  end

  defp callback_turnstile_ast do
    # Build a callback-mode AST with on_transition clauses
    on_transition_clauses = [
      {:match_arm,
       [
         pattern:
           {:tuple, [],
            [
              {:literal, [], :locked},
              {:literal, [], :coin},
              {:variable, [scope: :local], "_payload"},
              {:variable, [scope: :local], "data"}
            ]}
       ],
       [
         {:tuple, [],
          [
            {:literal, [], :ok},
            {:literal, [], :unlocked},
            {:binary_op, [op: "+"], [{:variable, [scope: :local], "data"}, {:literal, [], 1}]}
          ]}
       ]},
      {:match_arm,
       [
         pattern:
           {:tuple, [],
            [
              {:literal, [], :unlocked},
              {:literal, [], :push},
              {:variable, [scope: :local], "_payload"},
              {:variable, [scope: :local], "data"}
            ]}
       ], [{:tuple, [], [{:literal, [], :ok}, {:literal, [], :locked}, {:variable, [scope: :local], "data"}]}]},
      {:match_arm,
       [
         pattern:
           {:tuple, [],
            [
              {:variable, [scope: :local], "_state"},
              {:variable, [scope: :local], "_event"},
              {:variable, [scope: :local], "_payload"},
              {:variable, [scope: :local], "data"}
            ]}
       ], [{:tuple, [], [{:literal, [], :ok}, {:literal, [], :__same__}, {:variable, [scope: :local], "data"}]}]}
    ]

    {:container, [container_type: :fsm, name: "CallbackTurnstile", line: 1, on_transition: on_transition_clauses],
     [
       {:function_call, [name: "transition", from: "Locked", event: "coin", to: "Unlocked", event_kind: :normal], []},
       {:function_call, [name: "transition", from: "Unlocked", event: "push", to: "Locked", event_kind: :normal], []},
       {:function_call, [name: "transition", from: "Unlocked", event: "coin", to: "Unlocked", event_kind: :normal], []},
       {:function_call, [name: "transition", from: "Locked", event: "push", to: "Locked", event_kind: :normal], []}
     ]}
  end

  defp purge(mod) do
    :code.purge(mod)
    :code.delete(mod)
  end
end
