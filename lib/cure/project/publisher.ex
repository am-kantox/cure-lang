defmodule Cure.Project.Publisher do
  @moduledoc """
  Package tarball builder, signer, and uploader (v0.23.0).

  Used by `cure publish`. Walks the project root, assembles a
  reproducible gzipped tarball, delegates signing to
  `Cure.Project.Signing`, and uploads via
  `Cure.Project.Registry.publish/5`.

  Also supports an alternate Hex-compatible output via
  `build_hex_tarball/2` so existing Hex tooling can consume Cure
  packages.

  ## Tarball layout

      my_pkg-0.1.0/
        Cure.toml
        README.md
        LICENSE
        lib/
          *.cure
        docs/
          *.md

  The tarball is gzipped and its `sha256` is the canonical identity
  used by the registry, the lockfile, and the transparency log.
  """

  alias Cure.Project
  alias Cure.Project.{Registry, Signing}

  @type tarball :: binary()
  @type sha :: String.t()
  @type manifest :: map()

  # -- Building --------------------------------------------------------------

  @doc """
  Assemble a gzipped tarball from `root`. Returns
  `{:ok, bytes, sha256_hex, manifest}`.
  """
  @spec build_tarball(String.t()) :: {:ok, tarball(), sha(), manifest()} | {:error, term()}
  def build_tarball(root \\ ".") when is_binary(root) do
    with {:ok, project} <- Project.load(root) do
      files = collect_files(root)
      manifest = project_to_manifest(project)
      name_ver = "#{project.name}-#{project.version}"

      tar_entries =
        Enum.map(files, fn {relative, abs} ->
          body = File.read!(abs)
          {String.to_charlist(Path.join(name_ver, relative)), body}
        end)

      tmp = Path.join(System.tmp_dir!(), "cure_pkg_#{:erlang.unique_integer([:positive])}.tar.gz")

      case :erl_tar.create(String.to_charlist(tmp), tar_entries, [:compressed]) do
        :ok ->
          bytes = File.read!(tmp)
          _ = File.rm(tmp)
          sha = :crypto.hash(:sha256, bytes) |> Base.encode16(case: :lower)
          {:ok, bytes, sha, manifest}

        {:error, _} = err ->
          err
      end
    end
  end

  @doc """
  Sign and upload `{name, version}` from `root` using maintainer key
  `handle` and OAuth `token`.
  """
  @spec publish(String.t(), String.t(), String.t()) :: {:ok, map()} | {:error, term()}
  def publish(root, handle, token)
      when is_binary(root) and is_binary(handle) and is_binary(token) do
    with {:ok, bytes, sha, manifest} <- build_tarball(root),
         name = Map.get(manifest, "name"),
         version = Map.get(manifest, "version"),
         {:ok, signature} <- Signing.sign_tarball(handle, name, version, bytes),
         manifest = Map.put(manifest, "sha256", sha),
         manifest = Map.put(manifest, "publisher", handle),
         {:ok, response} <- Registry.publish(name, manifest, bytes, signature, token) do
      {:ok, Map.put(response, "sha256", sha)}
    end
  end

  @doc """
  Build a Hex-compatible tarball for cross-publishing.

  The output is a `.tar` (uncompressed) whose entries are:

      metadata.config    -- Erlang term with Hex metadata
      contents.tar.gz    -- gzipped tarball of the source tree
      VERSION            -- Hex tarball format version ("3")
      CHECKSUM           -- sha256 of the above three in canonical order

  Returns `{:ok, bytes}` (the `.tar` to feed into `mix hex.publish
  package --replace`).
  """
  @spec build_hex_tarball(String.t()) :: {:ok, binary()} | {:error, term()}
  def build_hex_tarball(root \\ ".") when is_binary(root) do
    with {:ok, project} <- Project.load(root) do
      files = collect_files(root)
      name_ver = "#{project.name}-#{project.version}"

      source_entries =
        Enum.map(files, fn {relative, abs} ->
          {String.to_charlist(Path.join(name_ver, relative)), File.read!(abs)}
        end)

      contents_tmp =
        Path.join(System.tmp_dir!(), "cure_hex_contents_#{:erlang.unique_integer([:positive])}.tar.gz")

      :ok = :erl_tar.create(String.to_charlist(contents_tmp), source_entries, [:compressed])
      contents = File.read!(contents_tmp)
      _ = File.rm(contents_tmp)

      metadata = hex_metadata(project, Enum.map(files, fn {rel, _} -> rel end))
      version_bin = "3"

      checksum_input = version_bin <> contents <> metadata
      checksum = :crypto.hash(:sha256, checksum_input) |> Base.encode16(case: :upper)

      outer_entries = [
        {~c"VERSION", version_bin},
        {~c"CHECKSUM", checksum},
        {~c"metadata.config", metadata},
        {~c"contents.tar.gz", contents}
      ]

      outer_tmp = Path.join(System.tmp_dir!(), "cure_hex_outer_#{:erlang.unique_integer([:positive])}.tar")

      :ok = :erl_tar.create(String.to_charlist(outer_tmp), outer_entries, [])
      bytes = File.read!(outer_tmp)
      _ = File.rm(outer_tmp)
      {:ok, bytes}
    end
  end

  # -- Helpers ---------------------------------------------------------------

  defp collect_files(root) do
    patterns = [
      "Cure.toml",
      "README.md",
      "LICENSE",
      "lib/**/*.cure",
      "lib/**/*.ex",
      "docs/**/*.md"
    ]

    patterns
    |> Enum.flat_map(fn p ->
      path = Path.join(root, p)
      Path.wildcard(path)
    end)
    |> Enum.uniq()
    |> Enum.filter(&File.regular?/1)
    |> Enum.map(fn abs -> {Path.relative_to(abs, root), abs} end)
  end

  defp project_to_manifest(project) do
    deps =
      project.dependencies
      |> Enum.map(fn dep ->
        %{
          "name" => Map.get(dep, :name, ""),
          "constraint" => Map.get(dep, :constraint) || Map.get(dep, :version) || ""
        }
      end)

    %{
      "name" => project.name,
      "version" => project.version,
      "dependencies" => deps
    }
  end

  defp hex_metadata(project, files) do
    # Hex uses Erlang term format for metadata.config. We render a
    # canonical subset by hand -- good enough for `mix hex.publish`.
    entries = [
      {:app, String.to_atom(project.name)},
      {:name, project.name},
      {:version, project.version},
      {:description, "Cure package cross-published via cure publish --hex"},
      {:licenses, ["MIT"]},
      {:files, Enum.map(files, &String.to_charlist/1)},
      {:requirements, []},
      {:build_tools, ["cure"]}
    ]

    entries
    |> Enum.map_join("\n", fn term -> :io_lib.format(~c"~p.", [term]) |> IO.iodata_to_binary() end)
  end
end
