defmodule Cure.PGO do
  @moduledoc """
  Profile-guided optimisation summary consumed by the v0.31.0 optimiser.

  Loads `Cure.PGO.Profile` files from disk, merges them, partitions
  per-MFA entries into hot and cold sets at the configured threshold,
  and exposes a struct that other optimisation passes (the inliner,
  the SMT translator) can query.

  ## Usage

      {:ok, pgo} = Cure.PGO.load("_build/cure/pgo")
      Cure.PGO.hot?(pgo, {:my_mod, :my_fn, 1})
      #=> true
      Cure.Optimizer.optimize(ast, pgo: pgo)

  ## Hot / cold classification

  Functions are sorted by `total_us` (when available; falling back
  to `calls`). The cumulative-fraction threshold is configurable via
  the `:hot_threshold` option (default `0.8`): the smallest set of
  functions whose cumulative cost reaches the threshold is the hot
  set; everything else is cold.

  ## Strict opt-in

  This module is **never** consulted unless the user explicitly opts
  in via `cure compile --pgo` (or `optimize_opts: [pgo: ...]`).
  Auto-discovery is intentionally absent: an existing
  `_build/cure/pgo/` directory will not affect compilation unless
  PGO is asked for.
  """

  alias Cure.PGO.Profile
  alias Cure.Pipeline.Events

  @default_hot_threshold 0.8

  @type mfa_key :: Profile.mfa_key()
  @type fn_key :: {atom(), non_neg_integer()}

  @type t :: %__MODULE__{
          modules: %{atom() => Profile.t()},
          hot: MapSet.t(mfa_key()),
          cold: MapSet.t(mfa_key()),
          branches: %{mfa_key() => %{non_neg_integer() => non_neg_integer()}},
          smt: %{mfa_key() => %{queries: non_neg_integer(), total_us: non_neg_integer()}},
          hot_threshold: float(),
          stale: [mfa_key()]
        }

  defstruct modules: %{},
            hot: MapSet.new(),
            cold: MapSet.new(),
            branches: %{},
            smt: %{},
            hot_threshold: @default_hot_threshold,
            stale: []

  @doc "Return an empty PGO summary -- no hot/cold sets, no entries."
  @spec empty(keyword()) :: t()
  def empty(opts \\ []) do
    %__MODULE__{
      hot_threshold: Keyword.get(opts, :hot_threshold, @default_hot_threshold)
    }
  end

  @doc """
  Load every `*.profile` file under `dir` and build a PGO summary.

  Returns `{:ok, pgo}` on success or `{:error, reason}` if `dir` is
  not a directory. Individual file failures are skipped (a
  `:pgo_load_failed` pipeline event is emitted) so a single
  corrupted profile cannot block the whole build.
  """
  @spec load(Path.t(), keyword()) :: {:ok, t()} | {:error, term()}
  def load(dir, opts \\ []) do
    threshold = Keyword.get(opts, :hot_threshold, @default_hot_threshold)
    emit? = Keyword.get(opts, :emit_events, true)

    case File.dir?(dir) do
      false ->
        {:error, {:not_a_directory, dir}}

      true ->
        profiles =
          dir
          |> Path.join("*.profile")
          |> Path.wildcard()
          |> Enum.flat_map(fn path ->
            case Profile.read(path) do
              {:ok, p} ->
                if emit?,
                  do: Events.emit(:type_checker, :pgo_loaded, {p.module, length(p.entries)}, Events.meta(path, 0))

                [p]

              {:error, reason} ->
                if emit?,
                  do: Events.emit(:type_checker, :pgo_load_failed, {path, reason}, Events.meta(path, 0))

                []
            end
          end)

        {:ok, build_summary(profiles, threshold)}
    end
  end

  @doc """
  Build a PGO summary from an explicit list of profiles. Useful for
  tests and for in-memory roundtrips that do not touch disk.
  """
  @spec from_profiles([Profile.t()], keyword()) :: t()
  def from_profiles(profiles, opts \\ []) when is_list(profiles) do
    threshold = Keyword.get(opts, :hot_threshold, @default_hot_threshold)
    build_summary(profiles, threshold)
  end

  @doc "Is the given MFA in the hot set?"
  @spec hot?(t(), mfa_key()) :: boolean()
  def hot?(%__MODULE__{hot: set}, mfa), do: MapSet.member?(set, mfa)

  @doc "Is the given MFA in the cold set?"
  @spec cold?(t(), mfa_key()) :: boolean()
  def cold?(%__MODULE__{cold: set}, mfa), do: MapSet.member?(set, mfa)

  @doc """
  Classify a `function_def` AST node against the loaded summary.

  Looks up the function's `name`/arity inside `module` and returns
  one of `:hot`, `:cold`, or `:default` (the function is not in any
  loaded profile).

  When the loaded entry's `:def_hash` does not match the live
  function_def's meta hash, the entry is considered stale and the
  classification falls back to `:default`.
  """
  @spec classify(t(), atom(), atom(), non_neg_integer(), keyword()) ::
          :hot | :cold | :default
  def classify(%__MODULE__{} = pgo, module, name, arity, fn_meta \\ []) do
    mfa = {module, name, arity}

    cond do
      mfa in pgo.stale ->
        :default

      MapSet.member?(pgo.hot, mfa) ->
        if def_hash_matches?(pgo, mfa, fn_meta), do: :hot, else: :default

      MapSet.member?(pgo.cold, mfa) ->
        if def_hash_matches?(pgo, mfa, fn_meta), do: :cold, else: :default

      true ->
        :default
    end
  end

  defp def_hash_matches?(_pgo, _mfa, []), do: true

  defp def_hash_matches?(%__MODULE__{modules: mods}, {module, _, _} = mfa, fn_meta) do
    case Map.get(mods, module) do
      nil ->
        true

      %Profile{entries: entries} ->
        case Enum.find(entries, fn e -> e.mfa == mfa end) do
          nil -> true
          %{def_hash: 0} -> true
          %{def_hash: stored} -> stored == :erlang.phash2(fn_meta)
        end
    end
  end

  # -- Summary construction ---------------------------------------------------

  defp build_summary(profiles, threshold) do
    by_module = Map.new(profiles, fn p -> {p.module, p} end)

    entries =
      profiles
      |> Enum.flat_map(fn p -> p.entries end)
      |> Enum.sort_by(&entry_cost/1, :desc)

    total_cost = entries |> Enum.map(&entry_cost/1) |> Enum.sum()

    {hot, cold, _} =
      Enum.reduce(entries, {MapSet.new(), MapSet.new(), 0}, fn e, {h, c, acc} ->
        cost = entry_cost(e)
        new_acc = acc + cost

        cond do
          total_cost == 0 ->
            {h, MapSet.put(c, e.mfa), new_acc}

          acc / total_cost < threshold ->
            {MapSet.put(h, e.mfa), c, new_acc}

          true ->
            {h, MapSet.put(c, e.mfa), new_acc}
        end
      end)

    branches =
      Enum.reduce(entries, %{}, fn e, acc -> Map.put(acc, e.mfa, e.branches) end)

    smt =
      Enum.reduce(entries, %{}, fn e, acc ->
        Map.put(acc, e.mfa, %{queries: e.smt_queries, total_us: e.smt_total_us})
      end)

    %__MODULE__{
      modules: by_module,
      hot: hot,
      cold: cold,
      branches: branches,
      smt: smt,
      hot_threshold: threshold,
      stale: []
    }
  end

  defp entry_cost(%{total_us: us}) when us > 0, do: us
  defp entry_cost(%{calls: c}), do: c
end
