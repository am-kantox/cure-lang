defmodule Cure.Stdlib.Preload do
  @moduledoc """
  Load compiled Cure stdlib (and optionally example) BEAM modules into
  the running VM *without* adding their output directory to the global
  Erlang code path.

  ## Why not just `:code.add_patha/1`?

  Historically the preload helpers in `Cure.CLI`,
  `Mix.Tasks.Cure.Check.Examples` and the regression test suite all did:

      :code.add_patha(String.to_charlist(Path.expand("_build/cure/ebin")))

  That is convenient right up until `_build/cure/ebin` contains a stale
  lowercase `<name>.beam` left over from a previous compile with the old
  naming convention (for example, an older `examples/math.cure` produced
  a top-level `math.beam`). The moment the directory is on the code path,
  that stale file takes precedence over OTP's own `:math`, `:code`,
  `:lists`, etc., and any subsequent call to e.g. `:math.pi/0` raises
  `UndefinedFunctionError` because the stale module never exported it.

  Loading the beams directly via `:code.load_binary/3` by their fully
  qualified `Cure.*` names side-steps the whole class of shadowing bugs:
  only modules whose file name starts with `Cure.` are ever considered,
  and the target directory is never added to the global code path.

  ## Module discovery and grouping

  The set of stdlib modules is *not* hard-coded. At Elixir compile time
  this module walks `lib/std/*.cure`, extracts the declared `mod Std.X`
  name, and the first `fn __group__() -> Atom = :<group>` declaration
  in each source (see `docs/STDLIB.md`). Modules without a `__group__/0`
  declaration are assigned to `:core` by default.

  The resulting `%{module => group}` map is baked into the module via
  `@external_resource` so any change to `lib/std/*.cure` invalidates the
  compile cache. When `lib/std/` is not available (e.g. a packaged
  release), `stdlib_modules/1` falls back to scanning
  `_build/cure/ebin` for `Cure.Std.*.beam` files and calling the
  exported `__group__/0` on each module.

  ## Kinds

  `stdlib_modules/1` and `preload/1` both accept a `kind` argument that
  filters modules by group:

    * `:none` (the default) -- empty list; nothing is loaded unless the
      caller asks for it explicitly.
    * `:all` -- every `Cure.Std.*` module known to the build.
    * `:core | :collections | :text | :numeric | :system |
       :concurrency | :option | :test | :network` -- the modules tagged
      with that group.
    * A list combining any of the group atoms; the union of their
      memberships with duplicates stripped.

  The "explicit over implicit" default means the REPL starts with no
  stdlib modules pre-imported unless `.cure.repl.toml` (or the caller)
  says otherwise; CLI entry points like `cure run` and
  `mix cure.check.examples` pass `kind: :all` to preserve their
  historical behaviour.
  """

  alias Cure.Stdlib.Paths

  require Logger

  @default_examples_ebin "_build/cure/ex_ebin"

  @stdlib_source_dir Path.expand("../../../lib/std", __DIR__)

  @known_groups [
    :core,
    :collections,
    :text,
    :numeric,
    :system,
    :concurrency,
    :option,
    :test,
    :network
  ]

  # ---------------------------------------------------------------------------
  # Compile-time scan of lib/std/*.cure
  # ---------------------------------------------------------------------------

  @stdlib_sources (case File.ls(@stdlib_source_dir) do
                     {:ok, entries} ->
                       entries
                       |> Enum.filter(&String.ends_with?(&1, ".cure"))
                       |> Enum.map(&Path.join(@stdlib_source_dir, &1))
                       |> Enum.sort()

                     {:error, _} ->
                       []
                   end)

  for src <- @stdlib_sources do
    @external_resource src
  end

  @mod_regex ~r/^\s*(?:mod|proof|actor|fsm|sup|app)\s+([A-Za-z_][\w\.]*)/m
  @group_regex ~r/^\s*fn\s+__group__\s*\(\s*\)\s*->\s*Atom\s*=\s*:([a-z_][a-z0-9_]*)/m

  # Cure stdlib modules are emitted as plain Erlang-style atoms
  # (`:"Cure.Std.List"`), not as Elixir-prefixed atoms
  # (`:"Elixir.Cure.Std.List"`). The compiler's BEAM output uses the
  # former, so we build the same shape here.
  @std_module_groups (for path <- @stdlib_sources,
                          {:ok, src} <- [File.read(path)],
                          [_, declared] = Regex.run(@mod_regex, src) || [nil, nil],
                          is_binary(declared),
                          into: %{} do
                        module = String.to_atom("Cure." <> declared)

                        group =
                          case Regex.run(@group_regex, src) do
                            [_, g] -> String.to_atom(g)
                            _ -> :core
                          end

                        {module, group}
                      end)

  # ---------------------------------------------------------------------------
  # Public API
  # ---------------------------------------------------------------------------

  @typedoc "A stdlib group atom."
  @type group ::
          :core
          | :collections
          | :text
          | :numeric
          | :system
          | :concurrency
          | :option
          | :test
          | :network

  @typedoc """
  Kind filter understood by `stdlib_modules/1` and `preload/1`.

    * `:none` -- the empty selection (default everywhere).
    * `:all`  -- every known stdlib module.
    * a single `group` atom or a list of them -- the union of the
      modules tagged with any of those groups.
  """
  @type kind :: :all | :none | group() | [group()]

  @typedoc """
  Options for `preload/1`.

    * `:kind` -- which stdlib modules to load (see `t:kind/0`).
      Defaults to `:none` so callers must opt in.
    * `:examples` -- when `true`, also loads every `Cure.*.beam` found in
      the examples output directory. Defaults to `false`.
    * `:stdlib_ebin` -- override the stdlib beam directory. When not
      given, the full candidate list from `Cure.Stdlib.Paths.beam_dirs/0`
      is searched in order (`:cure` env override, bundled
      `priv/ebin`, legacy `_build/cure/ebin`). Passing a string here
      collapses the search to just that directory for callers that
      need deterministic behaviour (tests, scripts).
    * `:examples_ebin` -- override the examples beam directory. Defaults
      to `"_build/cure/ex_ebin"`.
    * `:source_jit` -- when `true` (the default), any module in
      `stdlib_modules(kind)` that failed to load from the BEAM
      candidates is recompiled from its `.cure` source via
      `Cure.Compiler.compile_and_load/2`. Disable for test harnesses
      that want a hard failure if the BEAMs are missing.
  """
  @type option ::
          {:kind, kind()}
          | {:examples, boolean()}
          | {:stdlib_ebin, String.t()}
          | {:examples_ebin, String.t()}
          | {:source_jit, boolean()}

  @doc """
  Return the canonical list of stdlib group atoms, in a stable order.

  Exposed so `Cure.REPL.Config` can validate user-supplied kinds.
  """
  @spec known_groups() :: [group()]
  def known_groups, do: @known_groups

  @doc """
  Return the baked-in `%{module => group}` map derived from
  `lib/std/*.cure` at Elixir compile time.

  The map is empty when `lib/std/` was unavailable during compilation;
  in that case `stdlib_modules/1` falls back to BEAM introspection.
  """
  @spec module_groups() :: %{module() => group()}
  def module_groups, do: @std_module_groups

  @doc """
  Return the list of stdlib modules matching `kind`.

  See `t:kind/0` for the accepted values. Default is `:none`.

  ## Examples

      iex> Cure.Stdlib.Preload.stdlib_modules(:none)
      []

      # :core returns modules tagged :core in their `__group__/0`:
      iex> :"Cure.Std.Core" in Cure.Stdlib.Preload.stdlib_modules(:core)
      true
  """
  @spec stdlib_modules(kind()) :: [module()]
  def stdlib_modules(kind \\ :none)

  def stdlib_modules(:none), do: []

  def stdlib_modules(:all), do: all_modules()

  def stdlib_modules(kind) when is_atom(kind) do
    validate_kind!(kind)
    filter_by_groups([kind])
  end

  def stdlib_modules(kinds) when is_list(kinds) do
    Enum.each(kinds, &validate_kind!/1)
    filter_by_groups(Enum.uniq(kinds))
  end

  def stdlib_modules(other) do
    raise ArgumentError, """
    invalid kind: #{inspect(other)}
    expected :all, :none, a group atom, or a list of group atoms.
    known groups: #{inspect(@known_groups)}
    """
  end

  @doc """
  Load compiled stdlib (and optionally example) modules.

  Always returns `:ok`, even when nothing can be loaded (the build directory
  may not exist yet during a fresh `mix deps.compile`). Modules already
  loaded into the VM are left alone.

  Resolution order for each module:

    1. Iterate `Cure.Stdlib.Paths.beam_dirs/0` and load the first
       matching `.beam`. When `:stdlib_ebin` is supplied explicitly,
       only that directory is consulted.
    2. Fall back to compiling the module from its `.cure` source in
       `Cure.Stdlib.Paths.source_dir/0` via
       `Cure.Compiler.compile_and_load/2`. Disable with
       `source_jit: false`.

  Source-JIT recovery guarantees that a release carrying the stdlib
  *sources* but not the BEAMs is still functional; failures are
  logged at `:debug` and swallowed, mirroring the BEAM-load path.

  See `t:option/0` for the accepted options. `:kind` defaults to `:none`
  so the caller must opt into loading.
  """
  @spec preload([option()]) :: :ok
  def preload(opts \\ []) do
    kind = Keyword.get(opts, :kind, :none)
    examples_ebin = Keyword.get(opts, :examples_ebin, @default_examples_ebin)
    include_examples? = Keyword.get(opts, :examples, false)
    source_jit? = Keyword.get(opts, :source_jit, true)

    candidate_dirs = stdlib_candidate_dirs(opts)

    load_stdlib(candidate_dirs, kind)
    if source_jit?, do: compile_missing_from_sources(kind)
    if include_examples?, do: load_cure_beams(examples_ebin)

    :ok
  end

  # Resolve the list of candidate BEAM directories for this preload
  # call. A caller-supplied `:stdlib_ebin` collapses the search to a
  # single directory (the legacy behaviour), while the default taps
  # into `Cure.Stdlib.Paths.beam_dirs/0` so every layout known to the
  # `Paths` module is consulted.
  defp stdlib_candidate_dirs(opts) do
    case Keyword.get(opts, :stdlib_ebin) do
      nil -> Paths.beam_dirs()
      dir when is_binary(dir) -> Enum.filter([dir], &File.dir?/1)
    end
  end

  # ---------------------------------------------------------------------------
  # Internals
  # ---------------------------------------------------------------------------

  defp validate_kind!(kind) when kind in [:all, :none], do: :ok

  defp validate_kind!(kind) when is_atom(kind) do
    if kind in @known_groups do
      :ok
    else
      raise ArgumentError, """
      unknown stdlib group: #{inspect(kind)}
      known groups: #{inspect(@known_groups)}
      """
    end
  end

  defp validate_kind!(other) do
    raise ArgumentError, "invalid kind entry: #{inspect(other)}"
  end

  defp filter_by_groups(groups) do
    # A plain list suffices here: at most 9 known groups, so `group in
    # wanted` is O(9) in the worst case. Using `MapSet` triggered a
    # Dialyzer `call_without_opaque` warning on the follow-up
    # `MapSet.member?/2` call.
    wanted = Enum.uniq(groups)

    all_modules_with_groups()
    |> Enum.filter(fn {_module, group} -> group in wanted end)
    |> Enum.map(fn {module, _group} -> module end)
    |> Enum.sort()
  end

  defp all_modules do
    all_modules_with_groups()
    |> Enum.map(fn {module, _group} -> module end)
    |> Enum.sort()
  end

  # Prefer the compile-time map; fall back to BEAM introspection when
  # `lib/std/` was unavailable at compile time (packaged releases).
  defp all_modules_with_groups do
    case @std_module_groups do
      map when map_size(map) > 0 ->
        Map.to_list(map)

      _ ->
        # Walk every candidate BEAM directory and union the results.
        # A module discovered in more than one directory keeps the
        # first (highest-priority) entry, matching load order.
        Paths.beam_dirs()
        |> Enum.flat_map(&discover_from_beams/1)
        |> Enum.uniq_by(fn {module, _group} -> module end)
    end
  end

  defp discover_from_beams(ebin) do
    if File.dir?(ebin) do
      ebin
      |> Path.join("Cure.Std.*.beam")
      |> Path.wildcard()
      |> Enum.map(fn path ->
        module =
          path
          |> Path.basename(".beam")
          |> String.to_atom()

        load_if_present(module, path)

        group =
          if function_exported?(module, :__group__, 0) do
            try do
              module.__group__()
            rescue
              _ -> :core
            catch
              _, _ -> :core
            end
          else
            :core
          end

        {module, group}
      end)
    else
      []
    end
  end

  # For each requested module, walk the candidate directories in
  # order and load from the first one that has a readable `.beam`.
  # Missing modules are left unloaded; the source-JIT fallback picks
  # them up later.
  defp load_stdlib([], _kind), do: :ok

  defp load_stdlib(candidate_dirs, kind) do
    Enum.each(stdlib_modules(kind), fn module ->
      load_from_candidates(module, candidate_dirs)
    end)
  end

  defp load_from_candidates(module, candidate_dirs) do
    Enum.find_value(candidate_dirs, :not_found, fn dir ->
      path = Path.join(dir, "#{module}.beam")

      with true <- File.exists?(path),
           :ok <- load_if_present(module, path) do
        :ok
      else
        _ -> false
      end
    end)
  end

  # Compile any module in `stdlib_modules(kind)` that is still not
  # loaded from its `.cure` source. This is the belt-and-braces
  # fallback for deployments that carry the sources (`priv/std/`) but
  # not the BEAMs (`priv/ebin/`). A failure on an individual module
  # is logged at `:debug` and swallowed; the caller will get a
  # `:undef` at call time, same as before.
  @doc false
  @spec compile_missing_from_sources(kind()) :: :ok
  def compile_missing_from_sources(kind) do
    case Paths.source_dir() do
      nil ->
        :ok

      source_dir ->
        if compiler_available?() do
          Enum.each(stdlib_modules(kind), fn module ->
            unless module_loaded?(module) do
              jit_compile_module(module, source_dir)
            end
          end)
        end

        :ok
    end
  end

  defp compiler_available? do
    Code.ensure_loaded?(Cure.Compiler) and
      function_exported?(Cure.Compiler, :compile_and_load, 2)
  end

  defp module_loaded?(module) do
    case :code.is_loaded(module) do
      {:file, _} -> true
      _ -> Code.ensure_loaded?(module)
    end
  end

  # Derive the stdlib source filename from the module atom. Our
  # stdlib convention is `lib/std/<lowercased-last-segment>.cure`
  # (e.g. `Cure.Std.List` -> `list.cure`). No deep search: a missing
  # source is a hard miss.
  defp jit_compile_module(module, source_dir) do
    case source_path_for(module, source_dir) do
      {:ok, path} ->
        case File.read(path) do
          {:ok, source} ->
            try do
              case Cure.Compiler.compile_and_load(source,
                     file: path,
                     emit_events: false,
                     check_types: false
                   ) do
                {:ok, _module} ->
                  :ok

                {:error, reason} ->
                  Logger.debug(fn ->
                    "stdlib JIT: failed to compile #{module} from #{path}: #{inspect(reason)}"
                  end)

                  :ok
              end
            rescue
              e ->
                Logger.debug(fn ->
                  "stdlib JIT: exception compiling #{module}: #{Exception.message(e)}"
                end)

                :ok
            end

          {:error, _reason} ->
            :ok
        end

      :not_found ->
        :ok
    end
  end

  defp source_path_for(module, source_dir) do
    basename =
      module
      |> Atom.to_string()
      |> String.split(".")
      |> List.last()
      |> String.downcase()

    path = Path.join(source_dir, basename <> ".cure")

    if File.exists?(path) do
      {:ok, path}
    else
      :not_found
    end
  end

  # Load any `Cure.*.beam` in the given directory. We restrict to the
  # `Cure.` prefix to make sure we never load a stale bare-name beam that
  # would shadow an OTP or Elixir module.
  defp load_cure_beams(ebin) do
    if File.dir?(ebin) do
      ebin
      |> Path.join("Cure.*.beam")
      |> Path.wildcard()
      |> Enum.each(fn path ->
        module =
          path
          |> Path.basename(".beam")
          |> String.to_atom()

        load_if_present(module, path)
      end)
    end
  end

  defp load_if_present(module, path) do
    with true <- File.exists?(path),
         {:ok, binary} <- File.read(path) do
      case :code.load_binary(module, String.to_charlist(path), binary) do
        {:module, ^module} -> :ok
        {:error, _reason} -> :ok
      end
    else
      _ -> :ok
    end
  end
end
