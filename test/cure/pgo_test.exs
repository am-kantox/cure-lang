defmodule Cure.PGOTest do
  use ExUnit.Case, async: false

  alias Cure.PGO
  alias Cure.PGO.{Profile, Recorder}

  # ============================================================================
  # Profile struct -- serialise / deserialise roundtrip
  # ============================================================================

  describe "Profile" do
    test "build_entry/2 fills defaults" do
      e = Profile.build_entry({:my_mod, :foo, 1})

      assert e.mfa == {:my_mod, :foo, 1}
      assert e.calls == 0
      assert e.total_us == 0
      assert e.branches == %{}
      assert e.smt_queries == 0
      assert e.smt_total_us == 0
      assert e.def_hash == 0
    end

    test "serialise / deserialise roundtrip" do
      p =
        Profile.new(:my_mod)
        |> Profile.add_entry(Profile.build_entry({:my_mod, :foo, 1}, calls: 100, total_us: 500, def_hash: 42))
        |> Profile.add_entry(Profile.build_entry({:my_mod, :bar, 0}, calls: 1, total_us: 1))

      bin = Profile.serialise(p)
      assert is_binary(bin)
      assert {:ok, p2} = Profile.deserialise(bin)
      assert p2.module == p.module
      assert p2.entries == p.entries
    end

    test "deserialise rejects garbage" do
      assert {:error, _} = Profile.deserialise(<<131, 100>>)
    end

    test "read / write roundtrip" do
      p = Profile.new(:demo) |> Profile.add_entry(Profile.build_entry({:demo, :go, 0}, calls: 7))
      path = Path.join(System.tmp_dir!(), "cure_pgo_test_#{System.unique_integer([:positive])}.profile")

      try do
        assert :ok = Profile.write(p, path)
        assert {:ok, loaded} = Profile.read(path)
        assert loaded.module == :demo
        assert [%{calls: 7}] = loaded.entries
      after
        File.rm(path)
      end
    end
  end

  # ============================================================================
  # Recorder lifecycle
  # ============================================================================

  describe "Recorder" do
    setup do
      {:ok, pid} = Recorder.start_link([])
      on_exit(fn -> if Process.alive?(pid), do: GenServer.stop(pid) end)
      :ok
    end

    test "ticks accumulate per MFA" do
      Recorder.tick({:my_mod, :foo, 1})
      Recorder.tick({:my_mod, :foo, 1})
      Recorder.tick({:my_mod, :foo, 1})
      Recorder.tick_with_us({:my_mod, :bar, 0}, 250)

      snap = Recorder.snapshot()
      assert %Profile{} = snap[:my_mod]

      foo = Enum.find(snap[:my_mod].entries, fn e -> e.mfa == {:my_mod, :foo, 1} end)
      bar = Enum.find(snap[:my_mod].entries, fn e -> e.mfa == {:my_mod, :bar, 0} end)

      assert foo.calls == 3
      assert bar.calls == 1
      assert bar.total_us == 250
    end

    test "branch counters" do
      Recorder.tick({:m, :f, 0})
      Recorder.tick_branch({:m, :f, 0}, 7)
      Recorder.tick_branch({:m, :f, 0}, 7)
      Recorder.tick_branch({:m, :f, 0}, 11)

      snap = Recorder.snapshot()
      [entry] = snap[:m].entries
      assert entry.branches == %{7 => 2, 11 => 1}
    end

    test "smt counters" do
      Recorder.tick({:m, :f, 0})
      Recorder.tick_smt({:m, :f, 0}, 4, 1500)
      Recorder.tick_smt({:m, :f, 0}, 1, 500)

      snap = Recorder.snapshot()
      [entry] = snap[:m].entries
      assert entry.smt_queries == 5
      assert entry.smt_total_us == 2000
    end

    test "tick is a no-op when recorder is down" do
      GenServer.stop(Recorder)
      # Should not crash
      assert :ok = Recorder.tick({:nowhere, :nope, 0})
      assert Recorder.snapshot() == %{}
    end

    test "flush writes per-module profile and clears table" do
      Recorder.tick({:flushed, :foo, 0})
      Recorder.tick_with_us({:flushed, :bar, 0}, 100)

      dir = Path.join(System.tmp_dir!(), "cure_pgo_flush_#{System.unique_integer([:positive])}")

      try do
        {:ok, [path]} = Recorder.flush(dir)
        assert String.ends_with?(path, ".profile")

        {:ok, loaded} = Profile.read(path)
        assert loaded.module == :flushed
        assert length(loaded.entries) == 2

        # Table cleared
        assert Recorder.snapshot() == %{}
      after
        File.rm_rf!(dir)
      end
    end

    test "flush_all writes without clearing" do
      Recorder.tick({:retained, :foo, 0})
      dir = Path.join(System.tmp_dir!(), "cure_pgo_flushall_#{System.unique_integer([:positive])}")

      try do
        {:ok, [_path]} = Recorder.flush_all(dir)
        # Counters survive
        assert %{retained: %Profile{}} = Recorder.snapshot()
      after
        File.rm_rf!(dir)
      end
    end
  end

  # ============================================================================
  # Cure.PGO summary -- hot/cold classification
  # ============================================================================

  describe "summary" do
    test "empty/0 yields no hot or cold entries" do
      pgo = PGO.empty()
      assert MapSet.size(pgo.hot) == 0
      assert MapSet.size(pgo.cold) == 0
    end

    test "from_profiles/2 partitions at the 80/20 boundary" do
      # Top 80% of total cost should land in hot.
      profile =
        Profile.new(:m)
        |> Profile.add_entry(Profile.build_entry({:m, :a, 0}, calls: 80, total_us: 800))
        |> Profile.add_entry(Profile.build_entry({:m, :b, 0}, calls: 15, total_us: 150))
        |> Profile.add_entry(Profile.build_entry({:m, :c, 0}, calls: 5, total_us: 50))

      pgo = PGO.from_profiles([profile])
      assert PGO.hot?(pgo, {:m, :a, 0})
      assert PGO.cold?(pgo, {:m, :b, 0})
      assert PGO.cold?(pgo, {:m, :c, 0})
    end

    test "custom hot_threshold widens or narrows the hot set" do
      profile =
        Profile.new(:m)
        |> Profile.add_entry(Profile.build_entry({:m, :a, 0}, total_us: 80))
        |> Profile.add_entry(Profile.build_entry({:m, :b, 0}, total_us: 15))
        |> Profile.add_entry(Profile.build_entry({:m, :c, 0}, total_us: 5))

      tight = PGO.from_profiles([profile], hot_threshold: 0.5)
      loose = PGO.from_profiles([profile], hot_threshold: 0.99)

      # tight: only `a` is in the hot 50%
      assert PGO.hot?(tight, {:m, :a, 0})
      assert PGO.cold?(tight, {:m, :b, 0})

      # loose: both `a` and `b` reach the 99% threshold (a=80, a+b=95)
      assert PGO.hot?(loose, {:m, :a, 0})
      assert PGO.hot?(loose, {:m, :b, 0})
    end

    test "classify/4 respects def_hash for stale-profile detection" do
      meta = [name: "foo", line: 1]
      stored_hash = :erlang.phash2(meta)

      profile =
        Profile.new(:m)
        |> Profile.add_entry(Profile.build_entry({:m, :foo, 0}, calls: 100, def_hash: stored_hash))

      pgo = PGO.from_profiles([profile])

      assert :hot = PGO.classify(pgo, :m, :foo, 0, meta)
      # Mutated meta -> different hash -> classification should fall back.
      different_meta = [name: "foo", line: 999]
      assert :default = PGO.classify(pgo, :m, :foo, 0, different_meta)
    end
  end

  # ============================================================================
  # Disk roundtrip via PGO.load/2
  # ============================================================================

  describe "PGO.load/2" do
    test "loads every *.profile in a directory" do
      dir = Path.join(System.tmp_dir!(), "cure_pgo_load_#{System.unique_integer([:positive])}")
      File.mkdir_p!(dir)

      try do
        p1 =
          Profile.new(:mod_a)
          |> Profile.add_entry(Profile.build_entry({:mod_a, :foo, 0}, calls: 5))

        p2 =
          Profile.new(:mod_b)
          |> Profile.add_entry(Profile.build_entry({:mod_b, :bar, 0}, calls: 1))

        :ok = Profile.write(p1, Path.join(dir, "mod_a.profile"))
        :ok = Profile.write(p2, Path.join(dir, "mod_b.profile"))

        assert {:ok, pgo} = PGO.load(dir, emit_events: false)
        assert :mod_a in Map.keys(pgo.modules)
        assert :mod_b in Map.keys(pgo.modules)
      after
        File.rm_rf!(dir)
      end
    end

    test "missing directory returns an error" do
      assert {:error, {:not_a_directory, _}} =
               PGO.load("/nonexistent/path/" <> Integer.to_string(System.unique_integer([:positive])))
    end
  end

  # ============================================================================
  # Optimiser integration
  # ============================================================================

  describe "optimiser integration" do
    test "Inline.run/2 with a hot fn admits a larger ast_size" do
      # An 8-node body would normally exceed the default <= 5 cap; with a
      # hot classification it should be inlinable.
      ast = """
      mod CurePgoInlineTest
        fn big(x: Int) -> Int = x + 1 + 2 + 3 + 4 + 5
        fn use_it() -> Int = big(0)
      """

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(ast, file: "test", emit_events: false)
      {:ok, parsed} = Cure.Compiler.Parser.parse(tokens, file: "test", emit_events: false)

      # Build a PGO summary that classifies `big/1` as hot.
      profile =
        Profile.new(:"Cure.CurePgoInlineTest")
        |> Profile.add_entry(Profile.build_entry({:"Cure.CurePgoInlineTest", :big, 1}, calls: 100, total_us: 1000))

      pgo = PGO.from_profiles([profile], hot_threshold: 0.99)

      {_default_ast, default_count} = Cure.Optimizer.Inline.run(parsed, [])
      {_hot_ast, hot_count} = Cure.Optimizer.Inline.run(parsed, pgo: pgo, module: :"Cure.CurePgoInlineTest")

      # Default mode rejects (size > 5); hot mode accepts (size <= 12).
      assert default_count == 0
      assert hot_count >= 1
    end

    test "Optimizer.optimize/2 honours :pgo without breaking the pre-PGO path" do
      ast = """
      mod CurePgoOptimizeTest
        fn add1(x: Int) -> Int = x + 1
        fn use_it() -> Int = add1(41)
      """

      {:ok, tokens} = Cure.Compiler.Lexer.tokenize(ast, file: "test", emit_events: false)
      {:ok, parsed} = Cure.Compiler.Parser.parse(tokens, file: "test", emit_events: false)

      assert {:ok, _ast, stats} = Cure.Optimizer.optimize(parsed)
      assert is_map(stats)
      assert Map.has_key?(stats, :inline)
      assert Map.has_key?(stats, :monomorphise)

      # With PGO opt-in (empty summary): same correctness, no crash.
      assert {:ok, _ast, stats2} = Cure.Optimizer.optimize(parsed, pgo: PGO.empty())
      assert is_map(stats2)
    end
  end

  # ============================================================================
  # SMT translator -- pattern-aware regression
  # ============================================================================

  describe "SMT translator pgo_hint" do
    alias Cure.SMT.Translator

    test "default hint produces today's query" do
      ast =
        {:binary_op, [operator: :>], [{:variable, [], "x"}, {:literal, [subtype: :integer], 0}]}

      old = Translator.generate_query(ast, %{})
      new_default = Translator.generate_query(ast, %{}, :default)
      assert old == new_default
    end

    test "hot hint emits the arith-solver option" do
      ast =
        {:binary_op, [operator: :>], [{:variable, [], "x"}, {:literal, [subtype: :integer], 0}]}

      hot = Translator.generate_query(ast, %{}, :hot)
      assert hot =~ "(set-option :smt.arith.solver 6)"
    end

    test "cold hint omits the arith-solver option" do
      ast =
        {:binary_op, [operator: :>], [{:variable, [], "x"}, {:literal, [subtype: :integer], 0}]}

      cold = Translator.generate_query(ast, %{}, :cold)
      refute cold =~ "(set-option :smt.arith.solver 6)"
    end
  end
end
