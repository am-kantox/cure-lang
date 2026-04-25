defmodule Cure.PGO.Recorder do
  @moduledoc """
  Runtime counter table for the v0.31.0 profile-guided optimiser.

  Records per-MFA call counts, accumulated wall-clock time, branch
  counters, and SMT solver budget consumption into a public ETS
  table. `flush/1` (or `flush_all/1`) serialises the current
  snapshot to one `Cure.PGO.Profile` per module under the configured
  profile directory.

  ## Lifecycle

  Started under `Cure.Supervisor` lazily via `start_link/1` when
  the user invokes `cure run --record-profile`. The GenServer owns
  the ETS table; ticks themselves are direct ETS writes for
  minimal overhead.

  ## API

  * `tick/1` -- bump the call counter for `{mod, fun, arity}`.
  * `tick_with_us/2` -- bump call counter + total-us for an MFA.
  * `tick_branch/2` -- bump the count for `{mfa, site_id}`.
  * `tick_smt/3` -- accumulate SMT solver work for an MFA.
  * `flush/1` and `flush_all/1` -- write current state to disk and
    clear the table (or just write).

  All `tick_*` operations are safe to call when the recorder is not
  running -- they degrade silently to no-ops so that test fixtures
  that import instrumented code do not crash.
  """

  use GenServer

  alias Cure.PGO.Profile

  @table :cure_pgo_profiles
  @default_dir "_build/cure/pgo"

  # ETS row shapes
  # {{:mfa, mfa}, calls, total_us, smt_queries, smt_total_us}
  # {{:branch, mfa, site_id}, count}
  # {{:def_hash, mfa}, hash}

  @type mfa_key :: Profile.mfa_key()

  # -- Public API -------------------------------------------------------------

  @spec start_link(keyword()) :: GenServer.on_start()
  def start_link(opts \\ []) do
    GenServer.start_link(__MODULE__, opts, name: __MODULE__)
  end

  @doc "Whether the recorder GenServer is running."
  @spec running?() :: boolean()
  def running? do
    case :ets.whereis(@table) do
      :undefined -> false
      _ -> true
    end
  end

  @doc "Bump the call counter for an MFA."
  @spec tick(mfa_key()) :: :ok
  def tick({_, _, _} = mfa) do
    if running?() do
      :ets.update_counter(@table, {:mfa, mfa}, [{2, 1}], default_mfa_row(mfa))
      :ok
    else
      :ok
    end
  end

  @doc "Bump call counter and accumulate wall-clock microseconds."
  @spec tick_with_us(mfa_key(), non_neg_integer()) :: :ok
  def tick_with_us({_, _, _} = mfa, us) when is_integer(us) and us >= 0 do
    if running?() do
      :ets.update_counter(@table, {:mfa, mfa}, [{2, 1}, {3, us}], default_mfa_row(mfa))
      :ok
    else
      :ok
    end
  end

  @doc "Bump the branch counter for `(mfa, site_id)`."
  @spec tick_branch(mfa_key(), non_neg_integer()) :: :ok
  def tick_branch({_, _, _} = mfa, site_id) when is_integer(site_id) do
    if running?() do
      :ets.update_counter(@table, {:branch, mfa, site_id}, [{2, 1}], {{:branch, mfa, site_id}, 0})
      :ok
    else
      :ok
    end
  end

  @doc "Accumulate SMT solver work for an MFA."
  @spec tick_smt(mfa_key(), non_neg_integer(), non_neg_integer()) :: :ok
  def tick_smt({_, _, _} = mfa, queries, us)
      when is_integer(queries) and is_integer(us) and queries >= 0 and us >= 0 do
    if running?() do
      :ets.update_counter(@table, {:mfa, mfa}, [{4, queries}, {5, us}], default_mfa_row(mfa))
      :ok
    else
      :ok
    end
  end

  @doc "Record the function_def's meta hash for stale-profile detection."
  @spec set_def_hash(mfa_key(), non_neg_integer()) :: :ok
  def set_def_hash({_, _, _} = mfa, hash) when is_integer(hash) do
    if running?() do
      :ets.insert(@table, {{:def_hash, mfa}, hash})
      :ok
    else
      :ok
    end
  end

  @doc "Snapshot every entry; group by module."
  @spec snapshot() :: %{atom() => Profile.t()}
  def snapshot do
    if running?() do
      do_snapshot()
    else
      %{}
    end
  end

  @doc """
  Flush every module's profile to `<dir>/<module>.profile` and clear
  the table. `dir` defaults to `_build/cure/pgo`.
  """
  @spec flush(Path.t() | nil) :: {:ok, [Path.t()]} | {:error, term()}
  def flush(dir \\ nil) do
    if running?() do
      GenServer.call(__MODULE__, {:flush, dir || profile_dir()})
    else
      {:ok, []}
    end
  end

  @doc "Like `flush/1`, but does not clear the table afterwards."
  @spec flush_all(Path.t() | nil) :: {:ok, [Path.t()]} | {:error, term()}
  def flush_all(dir \\ nil) do
    if running?() do
      GenServer.call(__MODULE__, {:flush_all, dir || profile_dir()})
    else
      {:ok, []}
    end
  end

  @doc "Clear the recorder's ETS table without writing to disk."
  @spec reset() :: :ok
  def reset do
    if running?() do
      GenServer.call(__MODULE__, :reset)
    else
      :ok
    end
  end

  @doc "Default directory profiles are written to: `_build/cure/pgo`."
  @spec default_dir() :: Path.t()
  def default_dir, do: @default_dir

  defp profile_dir do
    System.get_env("CURE_PGO_DIR") || @default_dir
  end

  # -- GenServer callbacks ----------------------------------------------------

  @impl true
  def init(_opts) do
    table =
      :ets.new(@table, [:named_table, :public, :set, write_concurrency: true, read_concurrency: true])

    {:ok, %{table: table}}
  end

  @impl true
  def handle_call({:flush, dir}, _from, state) do
    result = do_flush(dir)

    case result do
      {:ok, _} -> clear_table()
      _ -> :ok
    end

    {:reply, result, state}
  end

  def handle_call({:flush_all, dir}, _from, state) do
    {:reply, do_flush(dir), state}
  end

  def handle_call(:reset, _from, state) do
    clear_table()
    {:reply, :ok, state}
  end

  # -- Internal ---------------------------------------------------------------

  defp default_mfa_row({_, _, _} = mfa) do
    {{:mfa, mfa}, 0, 0, 0, 0}
  end

  defp clear_table do
    if running?(), do: :ets.delete_all_objects(@table)
    :ok
  end

  defp do_snapshot do
    rows = :ets.tab2list(@table)

    {mfa_rows, branch_rows, hash_rows} =
      Enum.reduce(rows, {%{}, %{}, %{}}, fn
        {{:mfa, mfa}, calls, total_us, smt_q, smt_us}, {ms, bs, hs} ->
          {Map.put(ms, mfa, %{calls: calls, total_us: total_us, smt_queries: smt_q, smt_total_us: smt_us}), bs, hs}

        {{:branch, mfa, site_id}, count}, {ms, bs, hs} ->
          inner = Map.get(bs, mfa, %{})
          {ms, Map.put(bs, mfa, Map.put(inner, site_id, count)), hs}

        {{:def_hash, mfa}, hash}, {ms, bs, hs} ->
          {ms, bs, Map.put(hs, mfa, hash)}

        _, acc ->
          acc
      end)

    by_module =
      mfa_rows
      |> Enum.group_by(fn {{m, _, _}, _} -> m end)

    Enum.reduce(by_module, %{}, fn {module, entries}, acc ->
      profile = Profile.new(module)

      profile =
        Enum.reduce(entries, profile, fn {mfa, counters}, p ->
          entry =
            Profile.build_entry(mfa,
              def_hash: Map.get(hash_rows, mfa, 0),
              calls: counters.calls,
              total_us: counters.total_us,
              smt_queries: counters.smt_queries,
              smt_total_us: counters.smt_total_us,
              branches: Map.get(branch_rows, mfa, %{})
            )

          Profile.add_entry(p, entry)
        end)

      Map.put(acc, module, profile)
    end)
  end

  defp do_flush(dir) do
    File.mkdir_p!(dir)
    snap = do_snapshot()

    paths =
      Enum.map(snap, fn {module, profile} ->
        path = Path.join(dir, profile_filename(module))
        :ok = Profile.write(profile, path)
        path
      end)

    {:ok, paths}
  rescue
    e -> {:error, Exception.message(e)}
  end

  defp profile_filename(module) when is_atom(module) do
    safe = module |> Atom.to_string() |> String.replace([":", "/"], "_")
    safe <> ".profile"
  end
end
