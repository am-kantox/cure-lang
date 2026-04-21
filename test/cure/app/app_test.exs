defmodule Cure.App.AppTest do
  use ExUnit.Case, async: false

  alias Cure.Compiler.{Lexer, Parser, Codegen}
  alias Cure.App.{Compiler, Resource, Verifier}

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

  describe "app container parsing" do
    test "`app Name` with settings, hooks, and phases lowers into the app container" do
      ast =
        parse!("""
        app Demo
          vsn = "0.1.0"
          root = Demo.Root
          applications = [:logger]
          env = %{port: 4000}
          on_start
            (start_kind, args) -> :ok
          on_phase :init
            (phase_args, _kind, _start_args) -> :ok
        """)

      assert {:container, meta, []} = ast
      assert Keyword.get(meta, :container_type) == :app
      assert Keyword.get(meta, :name) == "Demo"
      assert {:literal, _, "0.1.0"} = Keyword.get(meta, :vsn)
      assert {:list, _, [{:literal, _, :logger}]} = Keyword.get(meta, :applications)
      assert {:map, _, _pairs} = Keyword.get(meta, :env)
      assert [{:match_arm, _, _}] = Keyword.get(meta, :on_start)
      assert [{:init, [{:match_arm, _, _}]}] = Keyword.get(meta, :on_phase)
    end
  end

  # -- Verifier --------------------------------------------------------------

  describe "Cure.App.Verifier" do
    test "passes on a minimal valid app" do
      ast = parse!("app OK")
      assert {:ok, _} = Verifier.verify(ast, emit_events: false)
    end

    test "rejects a non-atom in applications" do
      ast =
        parse!("""
        app Bad
          applications = [1, 2]
        """)

      assert {:error, errors} = Verifier.verify(ast, emit_events: false)
      assert Enum.any?(errors, &match?({:invalid_applications, _, _}, &1))
    end

    test "rejects a malformed root" do
      ast =
        parse!("""
        app Bad
          root = 42
        """)

      assert {:error, errors} = Verifier.verify(ast, emit_events: false)
      assert Enum.any?(errors, &match?({:invalid_root, _, _}, &1))
    end

    test "rejects a phase declared in TOML but not implemented" do
      ast =
        parse!("""
        app Demo
          on_phase :init
            (_a, _b, _c) -> :ok
        """)

      assert {:error, errors} =
               Verifier.verify(ast, emit_events: false, declared_phases: ["init", "warm_cache"])

      assert Enum.any?(errors, &match?({:start_phase_missing, :warm_cache, _}, &1))
    end

    test "rejects an on_phase clause that has no TOML entry" do
      ast =
        parse!("""
        app Demo
          on_phase :init
            (_a, _b, _c) -> :ok
          on_phase :extra
            (_a, _b, _c) -> :ok
        """)

      assert {:error, errors} =
               Verifier.verify(ast, emit_events: false, declared_phases: ["init"])

      assert Enum.any?(errors, &match?({:start_phase_unexpected, :extra, _}, &1))
    end
  end

  # -- Compiler --------------------------------------------------------------

  describe "Cure.App.Compiler" do
    setup do
      on_exit(fn -> for m <- [:"Cure.App.Demo", :"Cure.App.WithPhases"], do: purge(m) end)
      :ok
    end

    test "produces a loaded module exporting start/2 and stop/1" do
      ast =
        parse!("""
        app Demo
          on_start
            (start_kind, args) -> :ok
          on_stop
            (state) -> :ok
        """)

      {:ok, {:app, mod}} = Compiler.compile(ast, emit_events: false)
      assert mod == :"Cure.App.Demo"

      exports = mod.module_info(:exports)
      assert {:start, 2} in exports
      assert {:stop, 1} in exports
    end

    test "emits start_phase/3 only when on_phase clauses are present" do
      ast_no_phases = parse!("app Demo")
      {:ok, {:app, m1}} = Compiler.compile(ast_no_phases, emit_events: false)
      refute {:start_phase, 3} in m1.module_info(:exports)
      purge(m1)

      ast_phases =
        parse!("""
        app WithPhases
          on_phase :init
            (_a, _b, _c) -> :ok
        """)

      {:ok, {:app, m2}} = Compiler.compile(ast_phases, emit_events: false)
      assert {:start_phase, 3} in m2.module_info(:exports)
    end

    test "stop/1 returns :ok by default" do
      ast = parse!("app Demo")
      {:ok, {:app, mod}} = Compiler.compile(ast, emit_events: false)
      assert mod.stop(:irrelevant) == :ok
    end
  end

  # -- Codegen dispatch ------------------------------------------------------

  describe "Cure.Compiler.Codegen.compile_module/2 routes :app" do
    setup do
      on_exit(fn -> for m <- [:"Cure.App.Routed"], do: purge(m) end)
      :ok
    end

    test "returns {:app, module} when given a top-level app container" do
      ast = parse!("app Routed")
      assert {:ok, {:app, mod}} = Codegen.compile_module(ast, emit_events: false)
      assert mod == :"Cure.App.Routed"
    end

    test "surfaces verifier errors as {:error, {:app_verification_failed, _}}" do
      ast =
        parse!("""
        app Routed
          root = 42
        """)

      assert {:error, {:app_verification_failed, errors}} =
               Codegen.compile_module(ast, emit_events: false)

      assert Enum.any?(errors, &match?({:invalid_root, _, _}, &1))
    end
  end

  # -- Resource emitter ------------------------------------------------------

  describe "Cure.App.Resource" do
    @tag :tmp_dir
    test "writes a valid OTP .app file consultable by :file.consult/1", %{tmp_dir: tmp} do
      ast =
        parse!("""
        app Demo
          vsn = "0.4.2"
          applications = [:logger]
          env = %{port: 4000}
        """)

      {:container, meta, _} = ast

      project = %Cure.Project{
        name: "demo",
        version: "0.0.1",
        application: %{
          name: "demo",
          vsn: nil,
          description: "",
          applications: [],
          included_applications: [],
          start_phases: [],
          registered: [],
          env: %{}
        }
      }

      info = %{file: "lib/app.cure", name: "Demo", meta: meta}
      modules = [:"Demo.Hello"]

      assert :ok = Resource.write(info, modules, project, output_dir: tmp)
      app_path = Path.join(tmp, "demo.app")
      assert File.exists?(app_path)

      assert {:ok, [{:application, :demo, props}]} =
               :file.consult(String.to_charlist(app_path))

      assert props[:vsn] == ~c"0.4.2"
      assert :logger in props[:applications]
      assert :kernel in props[:applications]
      assert props[:env][:port] == 4000
      assert props[:mod] == {:"Cure.App.Demo", []}
    end
  end
end
