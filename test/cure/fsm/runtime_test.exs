defmodule Cure.FSM.RuntimeTest do
  use ExUnit.Case, async: false

  alias Cure.FSM.{Runtime, Builtins, Compiler}
  alias Cure.Compiler.BeamWriter

  # Compile and load the traffic light FSM for testing
  setup_all do
    ast =
      {:container, [container_type: :fsm, name: "TrafficLight", line: 1],
       [
         {:function_call, [name: "transition", from: "Red", event: "timer", to: "Green"], []},
         {:function_call, [name: "transition", from: "Green", event: "timer", to: "Yellow"], []},
         {:function_call, [name: "transition", from: "Yellow", event: "timer", to: "Red"], []},
         {:function_call, [name: "transition", from: "*", event: "emergency", to: "Red"], []}
       ]}

    {:ok, forms} = Compiler.compile(ast, emit_events: false)
    {:ok, _mod} = BeamWriter.compile_and_load(forms)
    :ok
  end

  # ============================================================================
  # Runtime: spawn, state, stop
  # ============================================================================

  describe "Runtime lifecycle" do
    test "spawn and get initial state" do
      {:ok, pid} = Runtime.spawn_fsm(:"Cure.FSM.TrafficLight")
      assert Process.alive?(pid)

      {:ok, {state, _data}} = Runtime.get_state(pid)
      assert state == :red

      Runtime.stop_fsm(pid)
    end

    test "spawn with name and lookup" do
      {:ok, pid} = Runtime.spawn_fsm(:"Cure.FSM.TrafficLight", name: "mylight")

      {:ok, found_pid} = Runtime.lookup("mylight")
      assert found_pid == pid

      Runtime.stop_fsm(pid)
    end

    test "stop removes from registry" do
      {:ok, pid} = Runtime.spawn_fsm(:"Cure.FSM.TrafficLight", name: "tostop")
      assert Runtime.alive?(pid)

      Runtime.stop_fsm(pid)
      Process.sleep(10)

      refute Runtime.alive?(pid)
      assert Runtime.lookup("tostop") == :error
    end

    test "list_fsms includes spawned FSMs" do
      {:ok, pid} = Runtime.spawn_fsm(:"Cure.FSM.TrafficLight", name: "listed")
      fsms = Runtime.list_fsms()
      assert Enum.any?(fsms, fn info -> info.pid == pid end)
      Runtime.stop_fsm(pid)
    end
  end

  # ============================================================================
  # Runtime: events and transitions
  # ============================================================================

  describe "Runtime events" do
    test "send_event transitions state" do
      {:ok, pid} = Runtime.spawn_fsm(:"Cure.FSM.TrafficLight")
      {:ok, {state, _}} = Runtime.get_state(pid)
      assert state == :red

      Runtime.send_event(pid, :timer)
      Process.sleep(10)
      {:ok, {state, _}} = Runtime.get_state(pid)
      assert state == :green

      Runtime.send_event(pid, :timer)
      Process.sleep(10)
      {:ok, {state, _}} = Runtime.get_state(pid)
      assert state == :yellow

      Runtime.stop_fsm(pid)
    end

    test "send_batch processes multiple events" do
      {:ok, pid} = Runtime.spawn_fsm(:"Cure.FSM.TrafficLight")
      Runtime.send_batch(pid, [:timer, :timer, :timer])
      Process.sleep(30)

      {:ok, {state, _}} = Runtime.get_state(pid)
      # Red -> Green -> Yellow -> Red
      assert state == :red

      Runtime.stop_fsm(pid)
    end

    test "wildcard transition works" do
      {:ok, pid} = Runtime.spawn_fsm(:"Cure.FSM.TrafficLight")
      Runtime.send_event(pid, :timer)
      Process.sleep(10)
      {:ok, {state, _}} = Runtime.get_state(pid)
      assert state == :green

      # Emergency from any state -> Red
      Runtime.send_event(pid, :emergency)
      Process.sleep(10)
      {:ok, {state, _}} = Runtime.get_state(pid)
      assert state == :red

      Runtime.stop_fsm(pid)
    end
  end

  # ============================================================================
  # Runtime: event history
  # ============================================================================

  describe "Runtime event history" do
    test "event history tracks sent events" do
      {:ok, pid} = Runtime.spawn_fsm(:"Cure.FSM.TrafficLight")
      Runtime.send_event(pid, :timer)
      Runtime.send_event(pid, :timer)
      Process.sleep(20)

      history = Runtime.event_history(pid)
      assert [:timer, :timer] = history

      Runtime.stop_fsm(pid)
    end

    test "get_info returns FSM metadata" do
      {:ok, pid} = Runtime.spawn_fsm(:"Cure.FSM.TrafficLight", name: "info_test")
      {:ok, info} = Runtime.get_info(pid)

      assert info.module == :"Cure.FSM.TrafficLight"
      assert info.name == "info_test"
      assert info.event_count == 0

      Runtime.send_event(pid, :timer)
      Process.sleep(10)
      {:ok, info} = Runtime.get_info(pid)
      assert info.event_count == 1

      Runtime.stop_fsm(pid)
    end
  end

  # ============================================================================
  # Runtime: automatic cleanup on crash
  # ============================================================================

  describe "Runtime process monitoring" do
    test "registry cleaned up when FSM process dies" do
      {:ok, pid} = Runtime.spawn_fsm(:"Cure.FSM.TrafficLight", name: "dying")
      assert {:ok, _} = Runtime.get_info(pid)

      # Kill the FSM process
      Process.exit(pid, :kill)
      Process.sleep(50)

      # Should be cleaned from registry
      assert Runtime.get_info(pid) == :error
      assert Runtime.lookup("dying") == :error
    end
  end

  # ============================================================================
  # Builtins (FFI bridge)
  # ============================================================================

  describe "Builtins" do
    test "fsm_spawn and fsm_state" do
      pid = Builtins.fsm_spawn(:"Cure.FSM.TrafficLight")
      assert is_pid(pid)

      state = Builtins.fsm_state(pid)
      assert state == :red

      Builtins.fsm_stop(pid)
    end

    test "fsm_send transitions state" do
      pid = Builtins.fsm_spawn(:"Cure.FSM.TrafficLight")
      Builtins.fsm_send(pid, :timer)
      Process.sleep(10)

      assert Builtins.fsm_state(pid) == :green
      Builtins.fsm_stop(pid)
    end

    test "fsm_is_alive" do
      pid = Builtins.fsm_spawn(:"Cure.FSM.TrafficLight")
      assert Builtins.fsm_is_alive(pid) == true
      Builtins.fsm_stop(pid)
      Process.sleep(10)
      assert Builtins.fsm_is_alive(pid) == false
    end

    test "fsm_history" do
      pid = Builtins.fsm_spawn(:"Cure.FSM.TrafficLight")
      Builtins.fsm_send(pid, :timer)
      Builtins.fsm_send(pid, :emergency)
      Process.sleep(20)

      history = Builtins.fsm_history(pid)
      assert [:timer, :emergency] = history

      Builtins.fsm_stop(pid)
    end

    test "fsm_spawn_named and fsm_lookup" do
      pid = Builtins.fsm_spawn_named(:"Cure.FSM.TrafficLight", "builtin_test")
      found = Builtins.fsm_lookup("builtin_test")
      assert found == pid
      Builtins.fsm_stop(pid)
    end
  end
end
