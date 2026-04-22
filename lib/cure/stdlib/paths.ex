defmodule Cure.Stdlib.Paths do
  @moduledoc """
  Resolve well-known locations for the Cure standard library.

  The stdlib lives in `lib/std/*.cure` inside the Cure repository, but
  host applications that depend on `:cure` (for example
  `:cure_site`) cannot rely on that path:

    * their working directory is their own project root, not Cure's;
    * production releases strip the `lib/` source tree and keep only
      compiled beams plus the `priv/` directory.

  This module provides a single resolution function used by
  `Cure.Types.Stdlib` (for `:t` signatures) and `Cure.REPL.Docs`
  (for `:doc` rendering). It falls through the following candidates in
  order:

    1. `Application.get_env(:cure, :stdlib_source_dir)` -- explicit
       override configured by the host (useful for tests or unusual
       layouts).
    2. `<priv_dir>/std` where `<priv_dir>` is `:code.priv_dir(:cure)`
       -- the canonical bundled location. Populated at compile time
       by `Mix.Tasks.Cure.BundleStdlib`; available verbatim in
       releases because `priv/` is part of every OTP application.
    3. `lib/std` relative to the current working directory -- the
       legacy fallback, kept so Cure's own tests and scripts keep
       working when run straight from the repository checkout.

  Only directories that actually exist on disk are returned.
  """

  @legacy_cwd_relative Path.join(["lib", "std"])

  @doc """
  Return every candidate stdlib source directory that currently exists,
  in search order. Callers that want a single canonical dir should use
  `source_dir/0`.
  """
  @spec source_dirs() :: [String.t()]
  def source_dirs do
    [configured_dir(), bundled_dir(), @legacy_cwd_relative]
    |> Enum.reject(&is_nil/1)
    |> Enum.uniq()
    |> Enum.filter(&File.dir?/1)
  end

  @doc """
  Return the first existing stdlib source directory, or `nil` when no
  candidate exists on disk. A `nil` result means neither Cure nor any
  of its consumers shipped the stdlib sources in a location we can
  discover -- callers should degrade gracefully (empty signature
  bundle, `:not_found` for `:doc`).
  """
  @spec source_dir() :: String.t() | nil
  def source_dir, do: List.first(source_dirs())

  @doc """
  Default destination for `Mix.Tasks.Cure.BundleStdlib` and its
  consumers. Exposed as a function (rather than a module attribute)
  so tests can stub it without pulling in Mix machinery.
  """
  @spec bundle_destination() :: String.t()
  def bundle_destination, do: Path.join(["priv", "std"])

  # ---------------------------------------------------------------------------

  @doc false
  @spec configured_dir() :: String.t() | nil
  def configured_dir do
    case Application.get_env(:cure, :stdlib_source_dir) do
      dir when is_binary(dir) -> dir
      _ -> nil
    end
  end

  @doc false
  @spec bundled_dir() :: String.t() | nil
  def bundled_dir do
    case :code.priv_dir(:cure) do
      {:error, _} -> nil
      priv -> Path.join(to_string(priv), "std")
    end
  end
end
