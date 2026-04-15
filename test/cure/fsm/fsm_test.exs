defmodule Cure.FSM.FSMTest do
  use ExUnit.Case, async: false

  alias Cure.FSM.{Verifier, Compiler}
  alias Cure.Compiler.BeamWriter
  alias Cure.Pipeline.Events

  # -- Helper: build a traffic light FSM AST -----------------------------------

  defp traffic_light_ast do
    {:container, [container_type: :fsm, name: "TrafficLight", line: 1],
     [
       {:function_call, [name: "transition", from: "Red", event: "timer", to: "Green"], []},
       {:function_call, [name: "transition", from: "Green", event: "timer", to: "Yellow"], []},
       {:function_call, [name: "transition", from: "Yellow", event: "timer", to: "Red"], []}
     ]}
  end

  defp traffic_light_with_wildcard_ast do
    {:container, [container_type: :fsm, name: "TrafficWild", line: 1],
     [
       {:function_call, [name: "transition", from: "Red", event: "timer", to: "Green"], []},
       {:function_call, [name: "transition", from: "Green", event: "timer", to: "Yellow"], []},
       {:function_call, [name: "transition", from: "Yellow", event: "timer", to: "Red"], []},
       {:function_call, [name: "transition", from: "*", event: "emergency", to: "Red"], []}
     ]}
  end

  defp with_terminal_ast do
    {:container, [container_type: :fsm, name: "ConnFSM", terminal_states: ["Closed", "Failed"], line: 1],
     [
       {:function_call, [name: "transition", from: "Open", event: "close", to: "Closed"], []},
       {:function_call, [name: "transition", from: "Open", event: "error", to: "Failed"], []}
     ]}
  end

  defp deadlock_ast do
    # Sink has no outgoing transitions and is not terminal
    {:container, [container_type: :fsm, name: "Deadlock", line: 1],
     [
       {:function_call, [name: "transition", from: "Active", event: "stop", to: "Sink"], []}
     ]}
  end

  defp unreachable_ast do
    # Island has no incoming transitions
    {:container, [container_type: :fsm, name: "Unreach", line: 1],
     [
       {:function_call, [name: "transition", from: "A", event: "go", to: "B"], []},
       {:function_call, [name: "transition", from: "B", event: "back", to: "A"], []},
       {:function_call, [name: "transition", from: "Island", event: "x", to: "Island"], []}
     ]}
  end

  # ============================================================================
  # Verifier Tests
  # ============================================================================

  describe "verifier - reachability" do
    test "traffic light: all states reachable" do
      assert {:ok, [{:verification_passed, "TrafficLight"}]} =
               Verifier.verify(traffic_light_ast(), emit_events: false)
    end

    test "with wildcard: all states reachable" do
      assert {:ok, _} = Verifier.verify(traffic_light_with_wildcard_ast(), emit_events: false)
    end

    test "unreachable state detected" do
      assert {:error, errors} = Verifier.verify(unreachable_ast(), emit_events: false)
      assert Enum.any?(errors, fn {type, _, _} -> type == :unreachable_state end)
    end
  end

  describe "verifier - deadlock freedom" do
    test "traffic light: no deadlocks (cyclic)" do
      assert {:ok, _} = Verifier.verify(traffic_light_ast(), emit_events: false)
    end

    test "terminal states exempt from deadlock check" do
      assert {:ok, _} = Verifier.verify(with_terminal_ast(), emit_events: false)
    end

    test "deadlock detected for non-terminal sink" do
      assert {:error, errors} = Verifier.verify(deadlock_ast(), emit_events: false)
      assert Enum.any?(errors, fn {type, _, _} -> type == :deadlock end)
    end
  end

  describe "verifier - pipeline events" do
    test "verification_passed event emitted" do
      Events.subscribe(:fsm_verifier, :verification_passed)

      {:ok, _} = Verifier.verify(traffic_light_ast(), emit_events: true)

      assert_receive {Cure.Pipeline.Events, :fsm_verifier, :verification_passed, "TrafficLight", _}
    end

    test "verification_failed event emitted" do
      Events.subscribe(:fsm_verifier, :verification_failed)

      {:error, _} = Verifier.verify(deadlock_ast(), emit_events: true)

      assert_receive {Cure.Pipeline.Events, :fsm_verifier, :verification_failed, _, _}
    end

    test "reachability_result events emitted per state" do
      Events.subscribe(:fsm_verifier, :reachability_result)

      {:ok, _} = Verifier.verify(traffic_light_ast(), emit_events: true)

      # Should get one event per state (Red, Green, Yellow)
      assert_receive {Cure.Pipeline.Events, :fsm_verifier, :reachability_result, _, _}
      assert_receive {Cure.Pipeline.Events, :fsm_verifier, :reachability_result, _, _}
      assert_receive {Cure.Pipeline.Events, :fsm_verifier, :reachability_result, _, _}
    end
  end

  # ============================================================================
  # Compiler Tests
  # ============================================================================

  describe "compiler - forms generation" do
    test "traffic light compiles to valid forms" do
      {:ok, forms} = Compiler.compile(traffic_light_ast(), emit_events: false)

      assert {:attribute, _, :module, :"Cure.FSM.TrafficLight"} = hd(forms)
      assert {:attribute, _, :behaviour, :gen_statem} = Enum.at(forms, 1)

      # Should have function forms for all gen_statem callbacks
      fn_names =
        forms
        |> Enum.filter(fn
          {:function, _, _, _, _} -> true
          _ -> false
        end)
        |> Enum.map(fn {:function, _, name, _, _} -> name end)

      assert :callback_mode in fn_names
      assert :start_link in fn_names
      assert :send_event in fn_names
      assert :get_state in fn_names
      assert :init in fn_names
      assert :handle_event in fn_names
    end
  end

  describe "compiler - gen_statem runtime" do
    test "traffic light FSM starts and transitions" do
      {:ok, forms} = Compiler.compile(traffic_light_ast(), emit_events: false)
      {:ok, mod} = BeamWriter.compile_and_load(forms)

      assert mod == :"Cure.FSM.TrafficLight"

      # Start the FSM
      {:ok, pid} = mod.start_link()

      # Initial state should be Red (first from state)
      {state, _data} = mod.get_state(pid)
      assert state == :red

      # Send timer -> should go to Green
      mod.send_event(pid, :timer)
      Process.sleep(10)
      {state, _} = mod.get_state(pid)
      assert state == :green

      # Send timer -> Yellow
      mod.send_event(pid, :timer)
      Process.sleep(10)
      {state, _} = mod.get_state(pid)
      assert state == :yellow

      # Send timer -> back to Red
      mod.send_event(pid, :timer)
      Process.sleep(10)
      {state, _} = mod.get_state(pid)
      assert state == :red

      GenServer.stop(pid)
    after
      purge(:"Cure.FSM.TrafficLight")
    end

    test "wildcard transitions work from any state" do
      {:ok, forms} = Compiler.compile(traffic_light_with_wildcard_ast(), emit_events: false)
      {:ok, mod} = BeamWriter.compile_and_load(forms)

      {:ok, pid} = mod.start_link()

      # Start at Red, go to Green
      mod.send_event(pid, :timer)
      Process.sleep(10)
      {state, _} = mod.get_state(pid)
      assert state == :green

      # Emergency from Green -> Red (wildcard)
      mod.send_event(pid, :emergency)
      Process.sleep(10)
      {state, _} = mod.get_state(pid)
      assert state == :red

      GenServer.stop(pid)
    after
      purge(:"Cure.FSM.TrafficWild")
    end
  end

  # ============================================================================
  # End-to-end from Cure source (via Codegen dispatch)
  # ============================================================================

  describe "end-to-end FSM via Codegen" do
    test "FSM container compiles through Codegen dispatch" do
      ast = traffic_light_ast()

      {:ok, forms} =
        Cure.Compiler.Codegen.compile_module(ast, emit_events: false)

      {:ok, mod} = BeamWriter.compile_and_load(forms)
      assert mod == :"Cure.FSM.TrafficLight"

      {:ok, pid} = mod.start_link()
      {state, _} = mod.get_state(pid)
      assert state == :red

      GenServer.stop(pid)
    after
      purge(:"Cure.FSM.TrafficLight")
    end
  end

  # -- Helpers -----------------------------------------------------------------

  defp purge(mod) do
    :code.purge(mod)
    :code.delete(mod)
  end
end
