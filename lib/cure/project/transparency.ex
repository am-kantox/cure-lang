defmodule Cure.Project.Transparency do
  @moduledoc """
  Client-side verifier for the Rekor-style transparency log (v0.23.0).

  The registry exposes an append-only log of every publish event at
  `GET /log`. Each entry is a JSON object:

      %{
        "index"      => non_neg_integer,
        "previous"   => sha256_hex,            # hash of the entry at `index - 1`
        "name"       => package_name,
        "version"    => version_string,
        "sha256"     => tarball_sha256_hex,
        "signature"  => base64_of_ed25519_sig,
        "publisher"  => maintainer_handle,
        "timestamp"  => iso8601,
        "hash"       => sha256_of_this_entry   # sha256(canonical_encoding_without_hash)
      }

  The client verifies, for any downloaded `{name, version, tarball}`:

  1. The log contains an entry matching the tarball's `sha256`.
  2. The entry's `hash` field is actually
     `sha256(canonical_encoding(entry - :hash))`.
  3. The entry's `previous` field matches the hash of the prior entry.

  ## Graceful degradation

  When the log URL is unreachable, `verify/3` returns
  `{:ok, :unverified}` instead of a hard error, and the pipeline emits
  `:transparency_log_unreachable` under code `E042`. Installs continue
  with a visible warning. Users who want strict verification can set
  `config :cure, strict_transparency: true`; in that mode, an
  unreachable log fails the install.

  ## Pipeline events

  Every verification attempt emits events on the `:registry` stage:

      :transparency_log_ok         -- entry verified
      :transparency_log_missing    -- tarball not on log
      :transparency_log_tampered   -- hash chain broken
      :transparency_log_unreachable -- server did not answer
  """

  alias Cure.Pipeline.Events
  alias Cure.Project.{Json, Registry}

  @type log_entry :: %{optional(String.t()) => term()}
  @type verification :: :ok | {:ok, :unverified} | {:error, term()}

  # -- Public API -------------------------------------------------------------

  @doc """
  Check that `{name, version, tarball_sha256}` appears in the
  transparency log.

  Returns `:ok` when the entry is present, hashes correctly, and chains
  back to the previous entry. Returns `{:ok, :unverified}` when the log
  is unreachable, unless `strict_transparency` is configured.
  """
  @spec verify(String.t(), String.t(), String.t()) :: verification()
  def verify(name, version, tarball_sha256)
      when is_binary(name) and is_binary(version) and is_binary(tarball_sha256) do
    case Registry.fetch_log_tip() do
      {:ok, %{"entries" => entries}} when is_list(entries) ->
        do_verify(entries, name, version, String.downcase(tarball_sha256))

      {:ok, other} ->
        emit(:transparency_log_unreachable, %{reason: {:malformed, other}})
        maybe_strict({:error, :malformed_log})

      {:error, reason} ->
        emit(:transparency_log_unreachable, %{reason: reason})
        maybe_strict({:error, {:unreachable, reason}})
    end
  end

  @doc """
  Canonical-encode a log entry (excluding its `hash` field) and compute
  the sha256 hex. Exposed for server-side publish tooling that needs to
  produce the same hash the client checks.
  """
  @spec entry_hash(log_entry()) :: String.t()
  def entry_hash(entry) when is_map(entry) do
    entry
    |> Map.delete("hash")
    |> canonical_encode()
    |> sha256_hex()
  end

  @doc """
  Run a full chain-integrity check over `entries` sorted by `index`
  ascending. Returns `:ok` or `{:error, {:chain_broken, index}}`.
  """
  @spec verify_chain([log_entry()]) :: :ok | {:error, {:chain_broken, non_neg_integer()}}
  def verify_chain(entries) when is_list(entries) do
    sorted = Enum.sort_by(entries, &Map.fetch!(&1, "index"))

    Enum.reduce_while(sorted, {:ok, nil}, fn entry, {:ok, prev_hash} ->
      this_hash = entry_hash(entry)
      declared_prev = Map.get(entry, "previous", "")
      declared_hash = Map.get(entry, "hash", "")

      cond do
        this_hash != declared_hash ->
          {:halt, {:error, {:chain_broken, Map.get(entry, "index", -1)}}}

        prev_hash != nil and declared_prev != prev_hash ->
          {:halt, {:error, {:chain_broken, Map.get(entry, "index", -1)}}}

        true ->
          {:cont, {:ok, this_hash}}
      end
    end)
    |> case do
      {:ok, _} -> :ok
      {:error, _} = err -> err
    end
  end

  # -- Internals --------------------------------------------------------------

  defp do_verify(entries, name, version, tarball_sha256) do
    matching =
      Enum.find(entries, fn
        %{"name" => n, "version" => v, "sha256" => s} ->
          n == name and v == version and String.downcase(s) == tarball_sha256

        _ ->
          false
      end)

    cond do
      matching == nil ->
        emit(:transparency_log_missing, %{name: name, version: version})
        {:error, :not_on_log}

      verify_chain(entries) != :ok ->
        emit(:transparency_log_tampered, %{name: name, version: version})
        {:error, :chain_tampered}

      true ->
        emit(:transparency_log_ok, %{name: name, version: version, index: Map.get(matching, "index", -1)})
        :ok
    end
  end

  defp canonical_encode(map) do
    # Canonicalisation: sort keys alphabetically, then emit the JSON
    # object by hand. `Map.new/1` does not preserve order, so we build
    # the literal bytes ourselves; this is what the server uses to hash
    # entries before they enter the log.
    pairs =
      map
      |> Enum.sort_by(fn {k, _} -> to_string(k) end)
      |> Enum.map_join(",", fn {k, v} ->
        Json.encode(to_string(k)) <> ":" <> Json.encode(v)
      end)

    "{" <> pairs <> "}"
  end

  defp sha256_hex(bytes), do: :crypto.hash(:sha256, bytes) |> Base.encode16(case: :lower)

  defp maybe_strict(err) do
    if Application.get_env(:cure, :strict_transparency, false) do
      err
    else
      {:ok, :unverified}
    end
  end

  defp emit(event_type, payload) do
    try do
      Events.emit(:registry, event_type, payload, %{
        file: "transparency",
        line: 1,
        timestamp: System.monotonic_time(:microsecond)
      })
    rescue
      _ -> :ok
    end
  end
end
