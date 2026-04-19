defmodule Cure.Project.Signing do
  @moduledoc """
  Ed25519 key management and tarball signing / verification (v0.23.0).

  Maintainers publish Cure packages with a detached Ed25519 signature
  over the tuple `name || "\\0" || version || "\\0" || sha256(tarball)`.
  The registry stores both the tarball and the signature; `cure deps`
  re-verifies the signature on every install against the maintainer's
  trusted public key.

  ## Key storage

  Keys live under `~/.cure/keys/`:

      ~/.cure/keys/<handle>.sec   -- private seed, `chmod 600`
      ~/.cure/keys/<handle>.pub   -- public key, `chmod 644`
      ~/.cure/keys/trusted.toml   -- trusted-key list (handle -> pub key)

  `<handle>` is the maintainer handle (GitHub OAuth or ad-hoc for dev
  work). The `trusted.toml` file is synced out-of-band; clients who
  install a package whose publisher is not in the local trust list get
  an `E041 Registry Signature Invalid` error.

  ## API overview

      {:ok, handle} = Cure.Project.Signing.generate_keypair("alice")
      {:ok, sig} = Cure.Project.Signing.sign_tarball("alice", name, ver, tar_bytes)
      :ok = Cure.Project.Signing.verify(handle, name, ver, tar_bytes, sig)

  The `:public_key`-based implementation uses OTP's built-in Ed25519
  support (available since OTP 24); no C deps are required.
  """

  @curve :ed25519
  @null_byte <<0>>

  @type handle :: String.t()
  @type sig_bytes :: binary()

  # -- Key generation ---------------------------------------------------------

  @doc """
  Generate a fresh Ed25519 keypair and persist it under `~/.cure/keys/`.

  Returns the handle the keypair was saved under.
  """
  @spec generate_keypair(handle()) :: {:ok, handle()} | {:error, term()}
  def generate_keypair(handle) when is_binary(handle) do
    {pub, priv} = :crypto.generate_key(:eddsa, @curve)
    ensure_keys_dir!()
    sec_path = Path.join(keys_dir(), handle <> ".sec")
    pub_path = Path.join(keys_dir(), handle <> ".pub")
    File.write!(sec_path, priv)
    File.write!(pub_path, pub)
    File.chmod!(sec_path, 0o600)
    File.chmod!(pub_path, 0o644)
    :ok = add_trusted(handle, pub)
    {:ok, handle}
  end

  @doc """
  Load a private key for `handle`. Returns `{:ok, priv_bytes}` or
  `{:error, :no_key}`.
  """
  @spec load_private(handle()) :: {:ok, binary()} | {:error, :no_key}
  def load_private(handle) when is_binary(handle) do
    case File.read(Path.join(keys_dir(), handle <> ".sec")) do
      {:ok, bytes} -> {:ok, bytes}
      {:error, _} -> {:error, :no_key}
    end
  end

  @doc """
  Load a public key for `handle`. Returns `{:ok, pub_bytes}` or
  `{:error, :no_key}`.
  """
  @spec load_public(handle()) :: {:ok, binary()} | {:error, :no_key}
  def load_public(handle) when is_binary(handle) do
    case File.read(Path.join(keys_dir(), handle <> ".pub")) do
      {:ok, bytes} -> {:ok, bytes}
      {:error, _} -> {:error, :no_key}
    end
  end

  # -- Signing / verifying ---------------------------------------------------

  @doc """
  Produce a detached signature for a package publication.

  The signing message is `name || NUL || version || NUL || sha256(tarball)`.
  """
  @spec sign_tarball(handle(), String.t(), String.t(), binary()) ::
          {:ok, sig_bytes()} | {:error, term()}
  def sign_tarball(handle, name, version, tarball)
      when is_binary(handle) and is_binary(name) and is_binary(version) and is_binary(tarball) do
    with {:ok, priv} <- load_private(handle) do
      msg = canonical_message(name, version, tarball)
      sig = :crypto.sign(:eddsa, :none, msg, [priv, @curve])
      {:ok, sig}
    end
  end

  @doc """
  Verify a publication signature against the trusted public key for
  `handle`. Returns `:ok` or `{:error, :signature_invalid}` /
  `{:error, :no_trusted_key}`.
  """
  @spec verify(handle(), String.t(), String.t(), binary(), sig_bytes()) ::
          :ok | {:error, :signature_invalid | :no_trusted_key}
  def verify(handle, name, version, tarball, signature)
      when is_binary(handle) and is_binary(name) and is_binary(version) and
             is_binary(tarball) and is_binary(signature) do
    case lookup_trusted(handle) do
      {:ok, pub} ->
        msg = canonical_message(name, version, tarball)

        if :crypto.verify(:eddsa, :none, msg, signature, [pub, @curve]) do
          :ok
        else
          {:error, :signature_invalid}
        end

      :error ->
        {:error, :no_trusted_key}
    end
  end

  # -- Trusted-key list ------------------------------------------------------

  @doc """
  Return the map of trusted handles to their public-key bytes.
  """
  @spec trusted_keys() :: %{handle() => binary()}
  def trusted_keys do
    path = trusted_path()

    case File.read(path) do
      {:ok, content} -> parse_trusted(content)
      {:error, _} -> %{}
    end
  end

  @doc """
  Add `handle` -> `pub_bytes` to the trusted-key list.
  """
  @spec add_trusted(handle(), binary()) :: :ok
  def add_trusted(handle, pub_bytes) when is_binary(handle) and is_binary(pub_bytes) do
    keys = Map.put(trusted_keys(), handle, pub_bytes)
    write_trusted(keys)
  end

  @doc """
  Remove `handle` from the trusted-key list.
  """
  @spec remove_trusted(handle()) :: :ok
  def remove_trusted(handle) when is_binary(handle) do
    keys = Map.delete(trusted_keys(), handle)
    write_trusted(keys)
  end

  defp lookup_trusted(handle) do
    case Map.fetch(trusted_keys(), handle) do
      {:ok, _} = ok -> ok
      :error -> :error
    end
  end

  defp write_trusted(keys) do
    ensure_keys_dir!()

    body =
      keys
      |> Enum.sort_by(fn {h, _} -> h end)
      |> Enum.map_join("\n", fn {h, pub} ->
        "#{h} = \"#{Base.encode16(pub, case: :lower)}\""
      end)

    File.write!(trusted_path(), body <> "\n")
    :ok
  end

  defp parse_trusted(content) do
    content
    |> String.split("\n", trim: true)
    |> Enum.reduce(%{}, fn line, acc ->
      case Regex.run(~r/^([^\s=]+)\s*=\s*"([0-9a-fA-F]+)"/, String.trim(line)) do
        [_, handle, hex] ->
          case Base.decode16(hex, case: :mixed) do
            {:ok, bytes} -> Map.put(acc, handle, bytes)
            _ -> acc
          end

        _ ->
          acc
      end
    end)
  end

  # -- Helpers ---------------------------------------------------------------

  defp canonical_message(name, version, tarball) do
    digest = :crypto.hash(:sha256, tarball)
    name <> @null_byte <> version <> @null_byte <> digest
  end

  defp keys_dir do
    System.user_home!() |> Path.join(".cure") |> Path.join("keys")
  end

  defp trusted_path do
    Path.join(keys_dir(), "trusted.toml")
  end

  defp ensure_keys_dir! do
    File.mkdir_p!(keys_dir())
    # Lock down the directory so siblings can't read keys.
    _ = File.chmod(keys_dir(), 0o700)
    :ok
  end
end
