defmodule Mix.Tasks.Cure.BundleStdlib do
  @moduledoc """
  Copy `lib/std/*.cure` stdlib sources into `priv/std/*.cure`.

  Host applications (e.g. `:cure_site`) that embed the Cure REPL need
  the stdlib `.cure` source files at runtime in order to resolve
  `:t Std.List.map`, `:doc Std.List`, and short-name imports from
  `use Std.Mod`. The files are not reachable via the host's cwd, and
  production releases strip the `lib/` source tree -- so we stage a
  copy under `priv/std/`, which Mix always propagates into dependency
  builds and OTP releases.

  The task is idempotent: files are only re-copied when the source is
  newer than the destination (mtime comparison). It is a no-op when
  `lib/std/` is missing (for example, when Cure is consumed from a hex
  package whose `files:` list already bundled the stdlib somewhere
  else).

  Wired into the default `compile` alias in `mix.exs`, so end users do
  not need to invoke it explicitly.
  """

  use Mix.Task

  alias Cure.Stdlib.Paths

  @shortdoc "Bundle Cure stdlib sources into priv/std/"

  @source_dir Path.join(["lib", "std"])

  @impl Mix.Task
  def run(_args) do
    bundle(@source_dir, Paths.bundle_destination())
  end

  @doc false
  @spec bundle(String.t(), String.t()) :: {:ok, %{copied: non_neg_integer(), skipped: non_neg_integer()}}
  def bundle(source_dir, dest_dir) do
    if File.dir?(source_dir) do
      File.mkdir_p!(dest_dir)

      source_dir
      |> Path.join("*.cure")
      |> Path.wildcard()
      |> Enum.reduce({:ok, %{copied: 0, skipped: 0}}, fn src, {:ok, counts} ->
        dst = Path.join(dest_dir, Path.basename(src))

        if should_copy?(src, dst) do
          File.cp!(src, dst)
          {:ok, %{counts | copied: counts.copied + 1}}
        else
          {:ok, %{counts | skipped: counts.skipped + 1}}
        end
      end)
    else
      {:ok, %{copied: 0, skipped: 0}}
    end
  end

  @doc false
  # Exposed for tests: true when `src` is newer than `dst` (or `dst`
  # does not exist yet). mtime comparison is deliberate so re-running
  # `mix compile` on an unchanged tree does not thrash the build.
  @spec should_copy?(String.t(), String.t()) :: boolean()
  def should_copy?(src, dst) do
    case {File.stat(src, time: :posix), File.stat(dst, time: :posix)} do
      {{:ok, src_stat}, {:ok, dst_stat}} -> src_stat.mtime > dst_stat.mtime
      {{:ok, _}, _} -> true
      _ -> false
    end
  end
end
