defmodule Cure.Actor.ActorTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser, Codegen}
  alias Cure.Actor.Runtime, as: ActorRuntime

  # -- Helpers ---------------------------------------------------------------

  defp parse!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  # Compile an actor container via the full pipeline. Returns the loaded
  # GenServer module atom.
  defp compile_actor!(source) do
    ast = parse!(source)
    {:ok, {:actor, mod_atom}} = Codegen.compile_module(ast, emit_events: false)
    mod_atom
  end

  defp purge(mod) do
    :code.purge(mod)
    :code.delete(mod)
    :code.purge(mod)
  end

  # -- Parser shape ----------------------------------------------------------

  describe "actor container parsing" do
    test "`actor Name` parses into a :container with container_type: :actor" do
      ast =
        parse!("""
        actor Empty
        """)

      assert {:container, meta, body} = ast
      assert Keyword.get(meta, :container_type) == :actor
      assert Keyword.get(meta, :name) == "Empty"
      assert body == []
    end

    test "lifecycle callbacks are hoisted onto the container meta" do
      ast =
        parse!("""
        actor Counter
          on_start
            (state) -> state
          on_message
            (:inc, n) -> n + 1
          on_stop
            (_r, _s) -> :ok
        """)

      assert {:container, meta, _body} = ast
      assert Keyword.get(meta, :container_type) == :actor

      # Each callback is stored as a flat list of {:match_arm, ...} nodes
      on_start = Keyword.get(meta, :on_start)
      on_message = Keyword.get(meta, :on_message)
      on_stop = Keyword.get(meta, :on_stop)

      assert [_] = on_start
      assert [_] = on_message
      assert [_] = on_stop
    end

    test "`with expr` header seeds the initial payload on container meta" do
      ast =
        parse!("""
        actor Seeded with 41
          on_message
            (:bump, n) -> n + 1
        """)

      assert {:container, meta, _} = ast
      assert {:literal, _, 41} = Keyword.get(meta, :init)
    end
  end

  # -- Runtime round-trip ----------------------------------------------------

  describe "actor codegen + runtime" do
    setup do
      on_exit(fn ->
        # Clean up any actors that didn't get purged via their own `after` blocks.
        for mod <- [:"Cure.Actor.Counter", :"Cure.Actor.Seeded", :"Cure.Actor.Notifier"] do
          purge(mod)
        end
      end)

      :ok
    end

    test "a counter actor handles :inc / :dec and exposes its payload" do
      src = """
      actor Counter with 0
        on_message
          (:inc, n) -> n + 1
          (:dec, n) -> n - 1
      """

      mod = compile_actor!(src)
      assert mod == :"Cure.Actor.Counter"

      {:ok, pid} = ActorRuntime.spawn_actor(mod, caller: self())

      assert mod.get_state(pid) == 0

      send(pid, :inc)
      send(pid, :inc)
      send(pid, :inc)
      _ = :sys.get_state(pid)
      assert mod.get_state(pid) == 3

      send(pid, :dec)
      _ = :sys.get_state(pid)
      assert mod.get_state(pid) == 2

      :ok = ActorRuntime.stop_actor(pid)
    after
      purge(:"Cure.Actor.Counter")
    end

    test "`notify/1` inside on_message targets the spawning caller" do
      src = """
      actor Notifier with 0
        on_message
          (:ping, n) ->
            notify(:pong)
            n
      """

      mod = compile_actor!(src)
      {:ok, pid} = ActorRuntime.spawn_actor(mod, caller: self())

      send(pid, :ping)
      assert_receive :pong, 500

      :ok = ActorRuntime.stop_actor(pid)
    after
      purge(:"Cure.Actor.Notifier")
    end

    test "on_start runs on init and may seed the payload" do
      src = """
      actor Seeded with 0
        on_start
          (state) -> 7
        on_message
          (:get, n) ->
            notify(n)
            n
      """

      mod = compile_actor!(src)
      {:ok, pid} = ActorRuntime.spawn_actor(mod, caller: self())

      assert mod.get_state(pid) == 7

      send(pid, :get)
      assert_receive 7, 500

      :ok = ActorRuntime.stop_actor(pid)
    after
      purge(:"Cure.Actor.Seeded")
    end

    test "runtime registry tracks live actors and removes them on stop" do
      src = """
      actor Counter with 0
        on_message
          (:inc, n) -> n + 1
      """

      mod = compile_actor!(src)
      {:ok, pid} = ActorRuntime.spawn_actor(mod, caller: self(), name: "counter-a")

      names = ActorRuntime.list_actors() |> Enum.map(& &1.name)
      assert "counter-a" in names

      assert {:ok, ^pid} = ActorRuntime.lookup("counter-a")

      ref = Process.monitor(pid)
      :ok = ActorRuntime.stop_actor(pid)
      assert_receive {:DOWN, ^ref, :process, ^pid, _}, 500

      assert ActorRuntime.lookup("counter-a") == :error
    after
      purge(:"Cure.Actor.Counter")
    end
  end
end
