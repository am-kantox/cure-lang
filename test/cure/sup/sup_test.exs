defmodule Cure.Sup.SupTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser, Codegen}
  alias Cure.Sup.{Compiler, Runtime, Verifier}

  # -- Helpers ---------------------------------------------------------------

  defp parse!(source) do
    {:ok, tokens} = Lexer.tokenize(source, emit_events: false)
    {:ok, ast} = Parser.parse(tokens, emit_events: false)
    ast
  end

  defp purge(mod) do
    :code.purge(mod)
    :code.delete(mod)
    :code.purge(mod)
  end

  # -- Parser shape ----------------------------------------------------------

  describe "sup container parsing" do
    test "`sup Name` with settings + children lowers into the supervisor container" do
      ast =
        parse!("""
        sup App.Root
          strategy = :one_for_one
          intensity = 5
          period = 10
          children
            Counter as counter
            Counter as counter_b (restart: :transient)
        """)

      assert {:container, meta, children} = ast
      assert Keyword.get(meta, :container_type) == :supervisor
      assert Keyword.get(meta, :name) == "App.Root"

      # Strategy, intensity, period are stored as raw Cure AST on meta
      assert {:literal, _, :one_for_one} = Keyword.get(meta, :strategy)
      assert {:literal, _, 5} = Keyword.get(meta, :intensity)
      assert {:literal, _, 10} = Keyword.get(meta, :period)

      assert [_, _] = children
      [first, second] = children
      assert {:child_spec, first_meta, []} = first
      assert Keyword.get(first_meta, :id) == "counter"
      assert Keyword.get(first_meta, :kind) == :worker

      assert {:child_spec, second_meta, []} = second
      assert {:literal, _, :transient} = Keyword.get(second_meta, :restart)
    end
  end

  # -- Verifier --------------------------------------------------------------

  describe "Cure.Sup.Verifier" do
    test "rejects unknown strategies" do
      ast =
        parse!("""
        sup Bad
          strategy = :pick_two
          children
            Counter as counter
        """)

      assert {:error, errors} = Verifier.verify(ast, emit_events: false)

      assert Enum.any?(errors, fn
               {:invalid_strategy, :pick_two, _} -> true
               _ -> false
             end)
    end

    test "rejects non-positive period" do
      ast =
        parse!("""
        sup Bad
          period = 0
          children
            Counter as counter
        """)

      assert {:error, errors} = Verifier.verify(ast, emit_events: false)

      assert Enum.any?(errors, fn
               {:invalid_period, _, _} -> true
               _ -> false
             end)
    end

    test "rejects duplicate child ids" do
      ast =
        parse!("""
        sup Dup
          children
            Counter as worker
            Counter as worker
        """)

      assert {:error, errors} = Verifier.verify(ast, emit_events: false)

      assert Enum.any?(errors, fn
               {:duplicate_child_id, "worker", _} -> true
               _ -> false
             end)
    end

    test "rejects unknown restart values" do
      ast =
        parse!("""
        sup BadRestart
          children
            Counter as worker (restart: :never)
        """)

      assert {:error, errors} = Verifier.verify(ast, emit_events: false)

      assert Enum.any?(errors, fn
               {:invalid_restart, :never, _} -> true
               _ -> false
             end)
    end

    test "passes on a minimal valid supervisor" do
      ast =
        parse!("""
        sup OK
          strategy = :one_for_all
          intensity = 0
          period = 1
          children
            Counter as worker (restart: :transient, shutdown: 1000)
        """)

      assert {:ok, _} = Verifier.verify(ast, emit_events: false)
    end
  end

  # -- Compiler + Runtime ----------------------------------------------------

  describe "Cure.Sup.Compiler + Runtime" do
    setup do
      on_exit(fn ->
        for mod <- [:"Cure.Sup.MinimalTree", :"Cure.Sup.WorkerTree", :"Cure.Actor.SupCounter"] do
          try do
            case Runtime.lookup(mod) do
              {:ok, _pid} -> Runtime.stop(mod)
              :error -> :ok
            end
          rescue
            _ -> :ok
          end

          purge(mod)
        end
      end)

      :ok
    end

    test "compiles a leaf supervisor with zero children" do
      ast =
        parse!("""
        sup MinimalTree
          strategy = :one_for_one
        """)

      {:ok, {:supervisor, mod}} = Compiler.compile(ast, emit_events: false)
      assert mod == :"Cure.Sup.MinimalTree"

      {:ok, pid} = Runtime.start(mod)
      assert is_pid(pid)
      assert Process.alive?(pid)
      assert Runtime.which_children(mod) == []

      :ok = Runtime.stop(mod)
    after
      purge(:"Cure.Sup.MinimalTree")
    end

    test "starts an actor child and keeps it alive under the supervisor" do
      # Compile the actor child first so the supervisor's child spec
      # points to a real loaded module.
      actor_ast =
        parse!("""
        actor SupCounter with 0
          on_message
            (:inc, n) -> n + 1
        """)

      {:ok, {:actor, actor_mod}} = Codegen.compile_module(actor_ast, emit_events: false)
      assert actor_mod == :"Cure.Actor.SupCounter"

      ast =
        parse!("""
        sup WorkerTree
          strategy = :one_for_one
          children
            SupCounter as counter (restart: :transient)
        """)

      {:ok, {:supervisor, sup_mod}} = Compiler.compile(ast, emit_events: false)
      {:ok, sup_pid} = Runtime.start(sup_mod)

      [{:counter, child_pid, :worker, _modules}] = Runtime.which_children(sup_mod)
      assert is_pid(child_pid)
      assert Process.alive?(child_pid)

      send(child_pid, :inc)
      send(child_pid, :inc)
      _ = :sys.get_state(child_pid)
      assert actor_mod.get_state(child_pid) == 2

      :ok = Runtime.stop(sup_mod)
      refute Process.alive?(sup_pid)
    after
      purge(:"Cure.Sup.WorkerTree")
      purge(:"Cure.Actor.SupCounter")
    end
  end
end
