defmodule CureSiteWeb.Commands.CureReplTest do
  # async: false -- we reach into `Application.put_env(:cure,
  # :repl_start_mfa, ...)`, which is a global switch shared with the
  # Mix task test suite.
  use ExUnit.Case, async: false

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

  describe "execute/2 dispatch (Mix-free)" do
    setup do
      parent = self()
      Application.put_env(:cure, :repl_start_mfa, {__MODULE__, :capture_repl_start, [parent]})
      on_exit(fn -> Application.delete_env(:cure, :repl_start_mfa) end)
      :ok
    end

    test "delegates to `Cure.REPL.start/1` with defaults merged in" do
      session = %Yeesh.Session{context: %{}}

      assert {:ok, _output, new_session} = CureRepl.execute([], session)
      assert new_session.mode == :normal

      assert_received {:repl_opts, opts}
      assert Keyword.get(opts, :raw) == false
      assert Keyword.get(opts, :error_device) == :stdio
      assert Keyword.get(opts, :history_path) == nil
      assert Keyword.get(opts, :theme) == :dark
    end

    test "user-supplied flags override the defaults (last occurrence wins)" do
      session = %Yeesh.Session{context: %{}}

      assert {:ok, _output, _session} =
               CureRepl.execute(["--theme=mono", "--mode=vi"], session)

      assert_received {:repl_opts, opts}
      assert Keyword.get(opts, :theme) == :mono
      assert Keyword.get(opts, :mode) == :vi
    end

    test "invalid switch values are surfaced as a banner prefix, not a crash" do
      session = %Yeesh.Session{context: %{}}

      assert {:ok, output, _session} = CureRepl.execute(["--theme=neon"], session)

      assert output =~ "repl:"
      assert output =~ "--theme"

      # The REPL still launches -- warnings are additive, not fatal.
      # Note that `OptionParser` collapses repeated `:string` switches
      # to last-wins, so `--theme=neon` overrides the default
      # `--theme=dark` *before* validation. The invalid value is
      # dropped by the translator, leaving no `:theme` override at
      # all; `Cure.REPL.start/1` then applies its own default.
      assert_received {:repl_opts, opts}
      refute Keyword.has_key?(opts, :theme)
    end

    test "does not depend on Mix at runtime" do
      # Sanity check: the module must not have pulled `Yeesh.MixCommand`
      # into its compiled behaviours list. The whole point of the
      # rewrite is to keep the `repl` command alive inside a prod
      # release where Mix is absent.
      behaviours =
        CureRepl.module_info(:attributes) |> Keyword.get_values(:behaviour) |> List.flatten()

      refute Yeesh.MixCommand in behaviours
    end
  end

  @doc false
  def capture_repl_start(parent, opts) do
    send(parent, {:repl_opts, opts})
    :ok
  end
end
