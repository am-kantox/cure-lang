defmodule Cure.Doc.MermaidTest do
  use ExUnit.Case, async: true

  alias Cure.Doc.Mermaid

  describe "FSM rendering" do
    test "emits stateDiagram-v2 with initial, edges, and event suffix" do
      transitions = [
        {:function_call, [name: "transition", from: "Locked", event: "coin", to: "Unlocked", event_kind: :normal], []},
        {:function_call, [name: "transition", from: "Unlocked", event: "push!", to: "Locked", event_kind: :hard], []}
      ]

      ast = {:container, [container_type: :fsm, name: "Turnstile", line: 1], transitions}
      out = Mermaid.render(ast)

      assert out =~ "stateDiagram-v2"
      assert out =~ "[*] --> Locked"
      assert out =~ "Locked --> Unlocked : coin"
      assert out =~ "Unlocked --> Locked : push!!"
    end

    test "renders terminal states into a sink edge" do
      transitions = [
        {:function_call, [name: "transition", from: "Running", event: "stop", to: "Done", event_kind: :normal], []}
      ]

      ast =
        {:container, [container_type: :fsm, name: "Job", terminal_states: ["Done"], line: 1], transitions}

      out = Mermaid.render(ast)
      assert out =~ "Done --> [*]"
    end

    test "returns nil for non-container input" do
      assert Mermaid.render({:literal, [], 42}) == nil
    end
  end

  describe "supervisor rendering" do
    test "renders children as labelled nodes linked from the supervisor" do
      children = [
        {:sup_child, [id: "worker", module: "WorkerActor", restart: :permanent], []},
        {:sup_child, [id: "echo", module: "EchoActor", restart: :transient], []}
      ]

      ast =
        {:container, [container_type: :sup, name: "Colony", strategy: :one_for_one, line: 1], children}

      out = Mermaid.render(ast)
      assert out =~ "graph TD"
      assert out =~ "Colony"
      assert out =~ "WorkerActor"
      assert out =~ "EchoActor"
      assert out =~ "Colony --> worker"
      assert out =~ "Colony --> echo"
    end
  end

  describe "application rendering" do
    test "labels the app node with vsn and draws the root edge" do
      ast =
        {:container,
         [
           container_type: :app,
           name: "CureAtelier",
           vsn: "0.27.0",
           root: "Atelier.Root",
           applications: ["logger", "cure"],
           line: 1
         ], []}

      out = Mermaid.render(ast)
      assert out =~ "graph LR"
      assert out =~ "CureAtelier"
      assert out =~ "vsn 0.27.0"
      assert out =~ "root: Atelier.Root"
      assert out =~ "logger"
      assert out =~ "cure"
    end
  end
end
