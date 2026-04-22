defmodule CureSiteWeb.Commands.CureReplTest do
  use ExUnit.Case, async: true

  alias CureSiteWeb.Commands.CureRepl

  describe "Yeesh.Command metadata" do
    test "implements the Yeesh.Command behaviour" do
      behaviours =
        CureRepl.module_info(:attributes) |> Keyword.get_values(:behaviour) |> List.flatten()

      assert Yeesh.Command in behaviours
    end

    test "name/0 surfaces a friendly short name" do
      assert CureRepl.name() == "repl"
    end

    test "description/0 is human-readable" do
      assert CureRepl.description() =~ "interactive Cure REPL"
    end

    test "usage/0 mentions the main option flags" do
      usage = CureRepl.usage()

      assert usage =~ "repl"
      assert usage =~ "--theme"
    end

    test "group/0 is Cure so help output bundles it with eval" do
      assert CureRepl.group() == "Cure"
    end

    test "completions/2 offers common option flags" do
      assert "--theme=dark" in CureRepl.completions("--theme=", %{})
      assert "--no-history" in CureRepl.completions("--no", %{})
      assert [] = CureRepl.completions("garbage-nothing-matches", %{})
    end
  end

  describe "MixCommand wiring" do
    test "wraps the `cure.repl` Mix task" do
      # The `Yeesh.MixCommand` macro stashes the task name in a module
      # attribute named `@mix_task`; it surfaces indirectly through
      # Mix.Task.get/1 the moment the command executes. We verify it
      # transitively here: the task module is resolvable once the host
      # Mix project has been loaded.
      assert Mix.Task.get("cure.repl") == Mix.Tasks.Cure.Repl
    end
  end
end
