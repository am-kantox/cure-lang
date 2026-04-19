defmodule Cure.FSM.FirstClassTest do
  @moduledoc """
  Tests for the v0.22.0 first-class FSM surface: the `%Cure.FSM.State{}`
  record shape, the three accepted `start_link/1` init shapes, outbound
  `Std.Fsm.notify/1` calls, `@notify_transitions`, the `on_start` and
  `on_stop` lifecycle hooks, and event payloads threaded through
  `send_event/3`.
  """
  use ExUnit.Case, async: false

  alias Cure.FSM.{Compiler, Runtime}
  alias Cure.FSM.State, as: FsmState

  # ============================================================================
  # Cure.FSM.State helpers (pure-function contract)
  # ============================================================================

  describe "Cure.FSM.State.from_init/1" do
    test "passes a struct through unchanged" do
      s = %FsmState{caller: self(), meta: %{a: 1}, payload: 42}
      assert FsmState.from_init(s) == s
    end

    test "lifts a keyword list into the struct" do
      s = FsmState.from_init(caller: self(), meta: %{a: 1}, payload: 42)
      assert %FsmState{caller: pid, meta: %{a: 1}, payload: 42} = s
      assert pid == self()
    end

    test "lifts a map into the struct" do
      s = FsmState.from_init(%{caller: self(), meta: :m, payload: :p})
      assert %FsmState{caller: pid, meta: :m, payload: :p} = s
      assert pid == self()
    end

    test "treats a bare value as the payload" do
      s = FsmState.from_init(7)
      assert %FsmState{caller: nil, meta: nil, payload: 7} = s
    end
  end

  describe "Cure.FSM.State.merge/2" do
    test "a full struct replaces wholesale" do
      s = %FsmState{caller: self(), meta: %{a: 1}, payload: 0}
      replacement = %FsmState{caller: nil, meta: %{b: 2}, payload: 9}
      assert FsmState.merge(s, replacement) == replacement
    end

    test "a partial map merges :payload and :meta; :caller survives" do
      s = %FsmState{caller: self(), meta: %{a: 1}, payload: 0}
      merged = FsmState.merge(s, %{payload: 10})
      assert %FsmState{caller: c, meta: %{a: 1}, payload: 10} = merged
      assert c == self()

      merged2 = FsmState.merge(s, %{payload: 10, meta: %{b: 2}})
      assert %FsmState{caller: c2, meta: %{b: 2}, payload: 10} = merged2
      assert c2 == self()
    end

    test "a bare value becomes the new payload" do
      s = %FsmState{caller: self(), meta: :m, payload: 0}
      merged = FsmState.merge(s, 99)
      assert %FsmState{caller: c, meta: :m, payload: 99} = merged
      assert c == self()
    end
  end

  describe "Cure.FSM.State.notify/2 and notify_self/1" do
    test "notify sends to caller when present" do
      s = %FsmState{caller: self()}
      FsmState.notify(s, :ping)
      assert_receive :ping, 100
    end

    test "notify is a no-op when caller is nil" do
      s = %FsmState{caller: nil}
      assert FsmState.notify(s, :ignored) == :no_caller
    end

    test "notify_self routes through the process-dictionary registered state" do
      FsmState.register_self(%FsmState{caller: self()})
      FsmState.notify_self(:ping_self)
      assert_receive :ping_self, 100
    end

    test "notify_self is a no-op outside an FSM process" do
      Process.delete(:cure_fsm_state)
      assert FsmState.notify_self(:ignored) == :no_caller
    end
  end

  # ============================================================================
  # Callback-mode FSM: three accepted init shapes on start_link/1
  # ============================================================================

  describe "start_link/1 init shape" do
    setup do
      mod = compile_ping()
      on_exit(fn -> purge(mod) end)
      {:ok, mod: mod}
    end

    test "accepts a fully-formed %FsmState{}", %{mod: mod} do
      init = %FsmState{caller: self(), meta: %{tag: :m}, payload: 100}
      {:ok, pid} = mod.start_link(init)

      {_, full} = mod.get_fsm_state(pid)
      assert full.caller == self()
      assert full.meta == %{tag: :m}
      assert full.payload == 100

      GenServer.stop(pid)
    end

    test "accepts a keyword list", %{mod: mod} do
      {:ok, pid} = mod.start_link(caller: self(), meta: :m, payload: 7)
      {_, full} = mod.get_fsm_state(pid)
      assert full.caller == self()
      assert full.meta == :m
      assert full.payload == 7

      GenServer.stop(pid)
    end

    test "accepts a bare payload", %{mod: mod} do
      {:ok, pid} = mod.start_link(99)
      {_, full} = mod.get_fsm_state(pid)
      assert full.payload == 99
      assert full.caller == nil
      assert full.meta == nil

      GenServer.stop(pid)
    end
  end

  # ============================================================================
  # send_event/3 with payload
  # ============================================================================

  describe "send_event/3 threads the event payload" do
    setup do
      mod = compile_echo()
      on_exit(fn -> purge(mod) end)
      {:ok, mod: mod}
    end

    test "event_payload reaches on_transition and updates the struct", %{mod: mod} do
      {:ok, pid} = mod.start_link(caller: self(), payload: nil)

      mod.send_event(pid, :echo, %{hello: :world})
      Process.sleep(20)

      {_, full} = mod.get_fsm_state(pid)
      assert full.payload == %{hello: :world}

      GenServer.stop(pid)
    end
  end

  # ============================================================================
  # @notify_transitions and on_transition sending `notify` manually
  # ============================================================================

  describe "@notify_transitions emits a transition message" do
    setup do
      mod = compile_notifier()
      on_exit(fn -> purge(mod) end)
      {:ok, mod: mod}
    end

    test "caller receives {:cure_fsm, pid, {:transition, from, ev, to, payload}}", %{
      mod: mod
    } do
      {:ok, pid} = mod.start_link(caller: self(), payload: 0)

      mod.send_event(pid, :go)
      assert_receive {:cure_fsm, ^pid, {:transition, :a, :go, :b, _}}, 200

      GenServer.stop(pid)
    end
  end

  # ============================================================================
  # on_start / on_stop lifecycle hooks
  # ============================================================================

  describe "on_start runs inside init and can seed state" do
    setup do
      mod = compile_with_on_start()
      on_exit(fn -> purge(mod) end)
      {:ok, mod: mod}
    end

    test "on_start is invoked and may return a partial update", %{mod: mod} do
      {:ok, pid} = mod.start_link(caller: self(), payload: 0)

      # on_start bumps payload to 999 and sends :started to the caller
      assert_receive :started, 200
      {_, full} = mod.get_fsm_state(pid)
      assert full.payload == 999

      GenServer.stop(pid)
    end
  end

  # ============================================================================
  # Runtime.spawn_fsm options: caller / meta / payload
  # ============================================================================

  describe "Runtime.spawn_fsm option mapping" do
    setup do
      mod = compile_ping()
      on_exit(fn -> purge(mod) end)
      {:ok, mod: mod}
    end

    test "caller/meta/payload opts become the initial struct", %{mod: mod} do
      {:ok, pid} =
        Runtime.spawn_fsm(mod,
          caller: self(),
          meta: %{env: :test},
          payload: :p0
        )

      {_, full} = mod.get_fsm_state(pid)
      assert full.caller == self()
      assert full.meta == %{env: :test}
      assert full.payload == :p0

      Runtime.stop_fsm(pid)
    end

    test "default when no init option given: spawner becomes caller", %{mod: mod} do
      {:ok, pid} = Runtime.spawn_fsm(mod)
      {_, full} = mod.get_fsm_state(pid)
      assert full.caller == self()

      Runtime.stop_fsm(pid)
    end

    test ":init option takes precedence", %{mod: mod} do
      {:ok, pid} =
        Runtime.spawn_fsm(mod, init: %FsmState{caller: nil, meta: :m, payload: :p})

      {_, full} = mod.get_fsm_state(pid)
      assert full.caller == nil
      assert full.meta == :m
      assert full.payload == :p

      Runtime.stop_fsm(pid)
    end

    test "legacy :data option still works", %{mod: mod} do
      {:ok, pid} = Runtime.spawn_fsm(mod, data: 42)
      {_, full} = mod.get_fsm_state(pid)
      assert full.payload == 42

      Runtime.stop_fsm(pid)
    end
  end

  # ============================================================================
  # AST helpers
  # ============================================================================

  # A minimal 2-state FSM that just bounces back to the same state. Used
  # for init-shape and basic introspection tests.
  defp compile_ping do
    clauses = [
      catch_all_clause()
    ]

    ast =
      {:container, [container_type: :fsm, name: "PingFsm", line: 1, on_transition: clauses],
       [
         {:function_call, [name: "transition", from: "Idle", event: "ping", to: "Idle", event_kind: :normal], []}
       ]}

    {:ok, {:callback_mode, mod}} = Compiler.compile(ast, emit_events: false)
    mod
  end

  # An FSM whose sole clause assigns the event payload to the struct's
  # payload, covering the send_event/3 path end-to-end.
  defp compile_echo do
    # (:idle, :echo, evp, state) -> {:ok, :idle, %{payload: evp}}
    echo_clause =
      {:match_arm,
       [
         pattern:
           {:tuple, [],
            [
              {:literal, [], :idle},
              {:literal, [], :echo},
              {:variable, [scope: :local], "evp"},
              {:variable, [scope: :local], "_state"}
            ]}
       ],
       [
         {:tuple, [],
          [
            {:literal, [], :ok},
            {:literal, [], :idle},
            {:map, [], [{{:literal, [], :payload}, {:variable, [scope: :local], "evp"}}]}
          ]}
       ]}

    clauses = [echo_clause, catch_all_clause()]

    ast =
      {:container, [container_type: :fsm, name: "EchoFsm", line: 1, on_transition: clauses],
       [
         {:function_call, [name: "transition", from: "Idle", event: "echo", to: "Idle", event_kind: :normal], []}
       ]}

    {:ok, {:callback_mode, mod}} = Compiler.compile(ast, emit_events: false)
    mod
  end

  # Two-state FSM with @notify_transitions that transitions :a -> :b on :go.
  defp compile_notifier do
    go_clause =
      {:match_arm,
       [
         pattern:
           {:tuple, [],
            [
              {:literal, [], :a},
              {:literal, [], :go},
              {:variable, [scope: :local], "_evp"},
              {:variable, [scope: :local], "state"}
            ]}
       ],
       [
         {:tuple, [],
          [
            {:literal, [], :ok},
            {:literal, [], :b},
            {:variable, [scope: :local], "state"}
          ]}
       ]}

    clauses = [go_clause, catch_all_clause()]

    ast =
      {:container,
       [
         container_type: :fsm,
         name: "NotifierFsm",
         line: 1,
         notify_transitions: true,
         on_transition: clauses
       ],
       [
         {:function_call, [name: "transition", from: "A", event: "go", to: "B", event_kind: :normal], []}
       ]}

    {:ok, {:callback_mode, mod}} = Compiler.compile(ast, emit_events: false)
    mod
  end

  # FSM with a single on_start clause that returns a partial update that
  # bumps :payload and notifies the caller.
  defp compile_with_on_start do
    on_start_clause =
      {:match_arm,
       [
         pattern: {:tuple, [], [{:variable, [scope: :local], "_state"}]}
       ],
       [
         {:block, [],
          [
            {:function_call, [name: "notify"], [{:literal, [], :started}]},
            {:tuple, [],
             [
               {:literal, [], :ok},
               {:map, [], [{{:literal, [], :payload}, {:literal, [], 999}}]}
             ]}
          ]}
       ]}

    clauses = [catch_all_clause()]

    ast =
      {:container,
       [
         container_type: :fsm,
         name: "OnStartFsm",
         line: 1,
         on_transition: clauses,
         on_start: [on_start_clause]
       ],
       [
         {:function_call, [name: "transition", from: "Idle", event: "ping", to: "Idle", event_kind: :normal], []}
       ]}

    {:ok, {:callback_mode, mod}} = Compiler.compile(ast, emit_events: false)
    mod
  end

  # The classic catch-all `(_, _, _, state) -> {:ok, :__same__, state}`
  # used to round out otherwise-sparse on_transition blocks.
  defp catch_all_clause do
    {:match_arm,
     [
       pattern:
         {:tuple, [],
          [
            {:variable, [scope: :local], "_state_atom"},
            {:variable, [scope: :local], "_event"},
            {:variable, [scope: :local], "_evp"},
            {:variable, [scope: :local], "state"}
          ]}
     ],
     [
       {:tuple, [],
        [
          {:literal, [], :ok},
          {:literal, [], :__same__},
          {:variable, [scope: :local], "state"}
        ]}
     ]}
  end

  defp purge(mod) do
    :code.purge(mod)
    :code.delete(mod)
  end
end
