defmodule Cure.Stdlib.Paths do
  @moduledoc """
  Resolve well-known locations for the Cure standard library.

  The stdlib lives in `lib/std/*.cure` (sources) and
  `_build/cure/ebin/Cure.Std.*.beam` (compiled modules) inside the Cure
  repository, but host applications that depend on `:cure` (for example
  `:cure_site`) cannot rely on either of those paths:

    * their working directory is their own project root, not Cure's;
    * production releases strip the `lib/` source tree and keep only
      compiled beams plus the `priv/` directory;
    * `_build/cure/ebin` is a build-time artefact and never ships
      with an OTP release.

  This module provides resolution functions used by
  `Cure.Types.Stdlib` (for `:t` signatures), `Cure.REPL.Docs` (for
  `:doc` rendering), and `Cure.Stdlib.Preload` (for loading the BEAMs
  that back qualified calls like `Std.List.map`). Both sources and
  BEAMs fall through the same pattern of candidates:

  ## Source directories (`source_dirs/0`, `source_dir/0`)

    1. `Application.get_env(:cure, :stdlib_source_dir)` -- explicit
       override configured by the host (useful for tests or unusual
       layouts).
    2. `<priv_dir>/std` where `<priv_dir>` is `:code.priv_dir(:cure)`
       -- the canonical bundled location. Populated at compile time
       by `Mix.Tasks.Cure.BundleStdlib`; available verbatim in
       releases because `priv/` is part of every OTP application.
    3. `$CURE_HOME/priv/std`, then `$CURE_HOME/lib/std` -- locations
       derived from the optional `CURE_HOME` environment variable.
       This is what powers the
       `export CURE_HOME=/path/to/cure && alias cure=$CURE_HOME/cure`
       workflow: the escript can be invoked from any directory and
       still resolve the stdlib without depending on the current
       working directory.
    4. `lib/std` relative to the current working directory -- the
       legacy fallback, kept so Cure's own tests and scripts keep
       working when run straight from the repository checkout.

  ## BEAM directories (`beam_dirs/0`, `beam_dir/0`)

    1. `Application.get_env(:cure, :stdlib_beam_dir)` -- explicit
       override (tests, alternative deployment layouts).
    2. `<priv_dir>/ebin` -- the canonical bundled location, populated
       by `Mix.Tasks.Cure.BundleStdlibBeams`. Rides along with OTP
       releases the same way `priv/std` does.
    3. `$CURE_HOME/priv/ebin`, then `$CURE_HOME/_build/cure/ebin` --
       locations derived from the `CURE_HOME` environment variable.
       The `priv/ebin` form matches a fully-bundled checkout (the
       output of `mix compile`); the `_build` form matches a fresh
       development checkout that has only ever run
       `mix cure.compile_stdlib`.
    4. `_build/cure/ebin` relative to the current working directory
       -- the legacy `mix cure.compile_stdlib` output, kept so
       checkouts that never produced a `priv/ebin/` bundle still work
       in development.

  Only directories that actually exist on disk are returned.
  """

  @legacy_cwd_source Path.join(["lib", "std"])
  @legacy_cwd_beam Path.join(["_build", "cure", "ebin"])

  @cure_home_env_var "CURE_HOME"

  @doc """
  Return every candidate stdlib source directory that currently exists,
  in search order. Callers that want a single canonical dir should use
  `source_dir/0`.
  """
  @spec source_dirs() :: [String.t()]
  def source_dirs do
    ([configured_source_dir(), bundled_source_dir()] ++
       cure_home_source_dirs() ++
       [@legacy_cwd_source])
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
  Return every candidate stdlib BEAM directory that currently exists,
  in search order. Used by `Cure.Stdlib.Preload` to locate compiled
  `Cure.Std.*.beam` modules in both development checkouts and
  packaged OTP releases. Callers that want a single canonical dir
  should use `beam_dir/0`.
  """
  @spec beam_dirs() :: [String.t()]
  def beam_dirs do
    ([configured_beam_dir(), bundled_beam_dir()] ++
       cure_home_beam_dirs() ++
       [@legacy_cwd_beam])
    |> Enum.reject(&is_nil/1)
    |> Enum.uniq()
    |> Enum.filter(&File.dir?/1)
  end

  @doc """
  Return the first existing stdlib BEAM directory, or `nil` when no
  candidate is present on disk. A `nil` result means the stdlib
  BEAMs were never bundled and no compile-time fallback exists; the
  REPL will still function for type inference (sources handle that),
  but any `Std.*.y` call will raise `:undef` until BEAMs are made
  available or the source-JIT fallback in `Cure.Stdlib.Preload`
  recovers them.
  """
  @spec beam_dir() :: String.t() | nil
  def beam_dir, do: List.first(beam_dirs())

  @doc """
  Default destination for `Mix.Tasks.Cure.BundleStdlib` and its
  consumers. Exposed as a function (rather than a module attribute)
  so tests can stub it without pulling in Mix machinery.
  """
  @spec bundle_destination() :: String.t()
  def bundle_destination, do: Path.join(["priv", "std"])

  @doc """
  Default destination for `Mix.Tasks.Cure.BundleStdlibBeams` and its
  consumers. Mirrors `bundle_destination/0` but points at the
  compiled-BEAM staging directory.
  """
  @spec beam_bundle_destination() :: String.t()
  def beam_bundle_destination, do: Path.join(["priv", "ebin"])

  # ---------------------------------------------------------------------------

  @doc false
  @spec configured_source_dir() :: String.t() | nil
  def configured_source_dir do
    case Application.get_env(:cure, :stdlib_source_dir) do
      dir when is_binary(dir) -> dir
      _ -> nil
    end
  end

  # Back-compat alias for external callers that used the pre-`beam`
  # naming. Deprecated but left in place to avoid churning every
  # caller in the same changeset.
  @doc false
  @deprecated "Use configured_source_dir/0"
  @spec configured_dir() :: String.t() | nil
  def configured_dir, do: configured_source_dir()

  @doc false
  @spec bundled_source_dir() :: String.t() | nil
  def bundled_source_dir do
    case :code.priv_dir(:cure) do
      {:error, _} -> nil
      priv -> Path.join(to_string(priv), "std")
    end
  end

  @doc false
  @deprecated "Use bundled_source_dir/0"
  @spec bundled_dir() :: String.t() | nil
  def bundled_dir, do: bundled_source_dir()

  @doc false
  @spec configured_beam_dir() :: String.t() | nil
  def configured_beam_dir do
    case Application.get_env(:cure, :stdlib_beam_dir) do
      dir when is_binary(dir) -> dir
      _ -> nil
    end
  end

  @doc false
  @spec bundled_beam_dir() :: String.t() | nil
  def bundled_beam_dir do
    case :code.priv_dir(:cure) do
      {:error, _} -> nil
      priv -> Path.join(to_string(priv), "ebin")
    end
  end

  @doc """
  Return the value of the `CURE_HOME` environment variable, normalised.

  Trailing whitespace is stripped and an empty value is treated as
  unset (returning `nil`). Use this to teach the `cure` escript where
  the canonical Cure checkout lives so it can locate the stdlib
  regardless of the caller's working directory.
  """
  @spec cure_home() :: String.t() | nil
  def cure_home do
    case System.get_env(@cure_home_env_var) do
      value when is_binary(value) ->
        case String.trim(value) do
          "" -> nil
          trimmed -> trimmed
        end

      _ ->
        nil
    end
  end

  @doc """
  Return the candidate stdlib BEAM directories derived from
  `CURE_HOME`, in priority order. Always returns a list (possibly
  empty); callers are expected to filter for existence themselves.
  """
  @spec cure_home_beam_dirs() :: [String.t()]
  def cure_home_beam_dirs do
    case cure_home() do
      nil ->
        []

      home ->
        [
          Path.join([home, "priv", "ebin"]),
          Path.join([home, "_build", "cure", "ebin"])
        ]
    end
  end

  @doc """
  Return the candidate stdlib source directories derived from
  `CURE_HOME`, in priority order. Always returns a list (possibly
  empty); callers are expected to filter for existence themselves.
  """
  @spec cure_home_source_dirs() :: [String.t()]
  def cure_home_source_dirs do
    case cure_home() do
      nil ->
        []

      home ->
        [
          Path.join([home, "priv", "std"]),
          Path.join([home, "lib", "std"])
        ]
    end
  end
end
