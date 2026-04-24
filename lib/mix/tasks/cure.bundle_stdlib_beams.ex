defmodule Mix.Tasks.Cure.BundleStdlibBeams do
  @moduledoc """
  Compile `lib/std/*.cure` into `priv/ebin/Cure.Std.*.beam`.

  Companion to `Mix.Tasks.Cure.BundleStdlib`, which stages stdlib
  *sources* into `priv/std/`. Host applications that embed Cure (most
  notably the browser REPL inside `:cure_site`) need not just the
  sources but also the compiled stdlib BEAMs reachable at runtime --
  `Std.List.map` lowers to `:'Cure.Std.List':map/...` in codegen, and
  that BEAM has to be loadable or every call raises `:undef`.

  Historically `mix cure.compile_stdlib` wrote the BEAMs to
  `_build/cure/ebin`, a build-time artefact that is not part of an OTP
  release. Staging the BEAMs under `priv/ebin/` instead gives us the
  same guarantees as `priv/std/`:

    * Mix propagates `priv/` into every dep build (`_build/<env>/lib/cure/priv/`).
    * `mix release` bundles `priv/` into the release tarball.
    * `:code.priv_dir(:cure)` resolves to the staged location at runtime.

  ## Idempotency

  Per-module mtime comparison: a `.cure` source triggers a recompile
  only when the expected `.beam` in the destination is missing or
  older than the source. The module name baked into the BEAM filename
  is parsed from the source's `mod ...` declaration (the same regex
  `Cure.Stdlib.Preload` uses at Elixir compile time). Sources we
  cannot classify are compiled unconditionally, since `Cure.Compiler`
  itself produces the canonical filename.

  ## No-op paths

  Leaves the tree untouched when `lib/std/` is missing (hex-packaged
  consumers whose `:files` strips the sources, tests that stub the
  project layout, etc.) and when `Cure.Compiler` is not yet available
  at the moment the task runs (very first dep compile). The caller
  that wired this into a `compile` alias is responsible for ordering
  it **after** the regular `compile` step so `Cure.Compiler` has been
  built.

  Wired into Cure's own `compile` alias in `mix.exs`, so end users do
  not need to invoke it explicitly.
  """

  use Mix.Task

  @shortdoc "Compile Cure stdlib sources into priv/ebin/"

  @source_dir Path.join(["lib", "std"])
  @mod_regex ~r/^\s*(?:mod|proof|actor|fsm|sup|app)\s+([A-Za-z_][\w\.]*)/m

  @impl Mix.Task
  def run(_args) do
    # `Cure.Compiler` emits pipeline events unconditionally (see
    # `Cure.Compiler.Lexer.maybe_emit_event/2`), so the
    # `Cure.Pipeline.Events.Registry` has to be running for any
    # compilation to succeed. Starting `:cure` as an OTP application
    # brings the registry up via `Cure.Application`. We call it even
    # when `compiler_available?/0` is false below; Mix handles the
    # "app not loaded yet" case gracefully.
    _ = ensure_cure_application_started()
    _ = bundle(@source_dir, default_destination())
    :ok
  end

  defp ensure_cure_application_started do
    if Code.ensure_loaded?(Mix.Task) and function_exported?(Mix.Task, :run, 2) do
      try do
        Mix.Task.run("app.start", [])
      rescue
        _ -> :ok
      catch
        _, _ -> :ok
      end
    else
      Application.ensure_all_started(:cure)
    end
  end

  @doc """
  Default output directory for compiled stdlib BEAMs.

  Resolves to `<priv>/ebin` relative to Cure's mix project root. Exposed
  as a function so tests can stub the path without pulling in Mix.
  """
  @spec default_destination() :: String.t()
  def default_destination, do: Path.join(["priv", "ebin"])

  @doc false
  @spec bundle(String.t(), String.t()) ::
          {:ok, %{compiled: non_neg_integer(), skipped: non_neg_integer(), errors: non_neg_integer()}}
  def bundle(source_dir, dest_dir) do
    cond do
      not File.dir?(source_dir) ->
        {:ok, %{compiled: 0, skipped: 0, errors: 0}}

      not compiler_available?() ->
        {:ok, %{compiled: 0, skipped: 0, errors: 0}}

      true ->
        File.mkdir_p!(dest_dir)

        source_dir
        |> Path.join("*.cure")
        |> Path.wildcard()
        |> Enum.sort()
        |> Enum.reduce({:ok, %{compiled: 0, skipped: 0, errors: 0}}, fn src, {:ok, counts} ->
          compile_one(src, dest_dir, counts)
        end)
    end
  end

  @doc false
  @spec compiler_available?() :: boolean()
  # The task is wired into a `compile` alias that runs *after* the
  # primary `compile` step, so by the time we get here the Cure
  # compiler should already be loaded. On the very first dep compile
  # however the task module can still be stale; guarding with a
  # function-exported check lets us degrade to a silent no-op instead
  # of crashing the entire compile.
  def compiler_available? do
    Code.ensure_loaded?(Cure.Compiler) and
      function_exported?(Cure.Compiler, :compile_file, 2)
  end

  @doc false
  @spec compile_one(String.t(), String.t(), map()) :: {:ok, map()}
  def compile_one(src, dest_dir, counts) do
    case expected_beam_path(src, dest_dir) do
      {:ok, beam_path} ->
        if should_compile?(src, beam_path) do
          do_compile(src, dest_dir, counts)
        else
          {:ok, %{counts | skipped: counts.skipped + 1}}
        end

      :unknown ->
        # Could not classify the module name from the source. Compile
        # unconditionally and let `Cure.Compiler` place the BEAM under
        # the canonical name.
        do_compile(src, dest_dir, counts)
    end
  end

  defp do_compile(src, dest_dir, counts) do
    case Cure.Compiler.compile_file(src, output_dir: dest_dir, emit_events: false) do
      {:ok, _module, _warnings} ->
        {:ok, %{counts | compiled: counts.compiled + 1}}

      {:error, _reason} ->
        # Surface the failure to the shell but keep processing the
        # remaining stdlib files so a single bad source does not
        # prevent the rest from being staged.
        if Code.ensure_loaded?(Mix) and function_exported?(Mix, :shell, 0) do
          Mix.shell().error("cure.bundle_stdlib_beams: failed to compile #{src}")
        end

        {:ok, %{counts | errors: counts.errors + 1}}
    end
  end

  @doc false
  @spec expected_beam_path(String.t(), String.t()) :: {:ok, String.t()} | :unknown
  def expected_beam_path(src, dest_dir) do
    case module_name_from_source(src) do
      {:ok, declared} ->
        {:ok, Path.join(dest_dir, "Cure.#{declared}.beam")}

      :unknown ->
        :unknown
    end
  end

  @doc false
  @spec module_name_from_source(String.t()) :: {:ok, String.t()} | :unknown
  def module_name_from_source(path) do
    with {:ok, contents} <- File.read(path),
         [_, declared] <- Regex.run(@mod_regex, contents) do
      {:ok, declared}
    else
      _ -> :unknown
    end
  end

  @doc false
  @spec should_compile?(String.t(), String.t()) :: boolean()
  # True when the BEAM is missing entirely or the source has been
  # touched more recently than the BEAM. mtime comparison is enough for
  # our purposes (same rationale as `Mix.Tasks.Cure.BundleStdlib.should_copy?/2`).
  def should_compile?(src, beam_path) do
    case {File.stat(src, time: :posix), File.stat(beam_path, time: :posix)} do
      {{:ok, src_stat}, {:ok, beam_stat}} -> src_stat.mtime > beam_stat.mtime
      {{:ok, _}, _} -> true
      _ -> false
    end
  end
end
