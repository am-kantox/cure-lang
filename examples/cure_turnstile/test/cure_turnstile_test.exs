defmodule CureTurnstileTest do
  use ExUnit.Case, async: true

  # ============================================================================
  # Raw FSM (gen_statem) tests
  # ============================================================================

  describe "raw Cure.FSM.Turnstile gen_statem" do
    @fsm :"Cure.FSM.Turnstile"

    test "start_link/0 initializes with nil payload" do
      {:ok, pid} = @fsm.start_link()
      {state, payload} = @fsm.get_state(pid)

      assert state == :locked
      # payload defaults to nil in the new FsmState contract
      assert payload == nil

      GenServer.stop(pid)
    end

    test "start_link/1 initializes with custom payload" do
      {:ok, pid} = @fsm.start_link(0)
      assert {:locked, 0} = @fsm.get_state(pid)

      GenServer.stop(pid)
    end

    test "coin do block increments data" do
      {:ok, pid} = @fsm.start_link(%Cure.FSM.State{payload: 0, meta: %{passages: 0}})

      @fsm.send_event(pid, :coin)
      _ = :sys.get_state(pid)
      assert {:unlocked, 1} = @fsm.get_state(pid)

      # second coin still increments
      @fsm.send_event(pid, :coin)
      _ = :sys.get_state(pid)
      assert {:unlocked, 2} = @fsm.get_state(pid)

      GenServer.stop(pid)
    end

    test "push preserves payload (no do block)" do
      {:ok, pid} = @fsm.start_link(%Cure.FSM.State{payload: 0, meta: %{passages: 0}})

      @fsm.send_event(pid, :coin)
      _ = :sys.get_state(pid)
      assert {:unlocked, 1} = @fsm.get_state(pid)

      @fsm.send_event(pid, :push)
      _ = :sys.get_state(pid)
      assert {:locked, 1} = @fsm.get_state(pid)

      GenServer.stop(pid)
    end

    test "push on locked stays locked, payload unchanged" do
      {:ok, pid} = @fsm.start_link(%Cure.FSM.State{payload: 0, meta: %{passages: 0}})

      @fsm.send_event(pid, :push)
      _ = :sys.get_state(pid)
      assert {:locked, 0} = @fsm.get_state(pid)

      GenServer.stop(pid)
    end

    test "full cycles accumulate coin count" do
      {:ok, pid} = @fsm.start_link(%Cure.FSM.State{payload: 0, meta: %{passages: 0}})

      for n <- 1..5 do
        @fsm.send_event(pid, :coin)
        _ = :sys.get_state(pid)
        assert {:unlocked, ^n} = @fsm.get_state(pid)

        @fsm.send_event(pid, :push)
        _ = :sys.get_state(pid)
        assert {:locked, ^n} = @fsm.get_state(pid)
      end

      GenServer.stop(pid)
    end
  end

  # ============================================================================
  # CureTurnstile wrapper tests
  # ============================================================================

  describe "CureTurnstile wrapper" do
    test "starts locked with zero counters" do
      {:ok, pid} = CureTurnstile.start_link()

      assert CureTurnstile.state(pid) == :locked
      assert CureTurnstile.stats(pid) == %{state: :locked, coins: 0, passages: 0}
    end

    test "insert_coin unlocks the turnstile" do
      {:ok, pid} = CureTurnstile.start_link()

      assert :ok = CureTurnstile.insert_coin(pid)
      assert CureTurnstile.unlocked?(pid)
    end

    test "push after coin locks and records a passage" do
      {:ok, pid} = CureTurnstile.start_link()

      CureTurnstile.insert_coin(pid)
      CureTurnstile.push(pid)

      assert CureTurnstile.state(pid) == :locked
      assert %{coins: 1, passages: 1} = CureTurnstile.stats(pid)
    end

    test "push on locked does not count a passage" do
      {:ok, pid} = CureTurnstile.start_link()

      CureTurnstile.push(pid)

      assert %{coins: 0, passages: 0} = CureTurnstile.stats(pid)
    end

    test "extra coins are counted via FSM data mutation" do
      {:ok, pid} = CureTurnstile.start_link()

      CureTurnstile.insert_coin(pid)
      CureTurnstile.insert_coin(pid)
      CureTurnstile.insert_coin(pid)
      CureTurnstile.push(pid)

      assert %{coins: 3, passages: 1} = CureTurnstile.stats(pid)
    end

    test "multiple full cycles" do
      {:ok, pid} = CureTurnstile.start_link()

      for _ <- 1..10 do
        CureTurnstile.insert_coin(pid)
        CureTurnstile.push(pid)
      end

      assert %{coins: 10, passages: 10, state: :locked} = CureTurnstile.stats(pid)
    end

    test "@notify_transitions reaches the caller" do
      {:ok, pid} = CureTurnstile.start_link()

      CureTurnstile.insert_coin(pid)

      # Exactly one transition message is expected: locked -> unlocked on :coin.
      assert_receive {:cure_fsm, ^pid, {:transition, :locked, :coin, :unlocked, 1}}, 500
    end
  end
end
