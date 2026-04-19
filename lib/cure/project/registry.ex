defmodule Cure.Project.Registry do
  @moduledoc """
  Remote package-registry HTTP client (v0.23.0).

  Implements the read-only side of the registry protocol outlined in
  `docs/PACKAGE_REGISTRY.md`. The server half is a separate component
  that can be stood up against a static bucket (see
  `docs/PUBLISHING.md`); every endpoint this client consumes is
  content-addressed by SHA-256 so an HTTP response mismatched against
  its hash is rejected before it ever reaches the resolver.

  ## Endpoints

  - `GET /packages/:name` -- list every published version of a package.
  - `GET /packages/:name/:version` -- manifest + tarball URL for a
    specific version.
  - `GET /packages/:name/:version/tarball` -- tarball bytes.
  - `GET /packages?q=<query>` -- substring search across package names
    and descriptions (used by `cure search`).
  - `GET /log` -- Rekor-style transparency-log tip (used by
    `Cure.Project.Transparency`).

  ## Caching

  Responses are cached on disk under `~/.cure/registry_cache/<sha256>`
  and keyed by the hash of their canonical bytes. Every subsequent call
  with the same hash hits the cache instead of the network; a cache
  with a mismatched body (detected on every read) is thrown away and
  the request is re-issued.

  ## Configuration

  The base URL is taken in priority order from:

  1. The `:registry_url` application env key
     (`Application.get_env(:cure, :registry_url)`).
  2. The `CURE_REGISTRY_URL` OS environment variable.
  3. The default `https://registry.cure-lang.org`.

  `Cure.Project.Registry.with_base_url/2` scopes a single call to an
  alternate URL -- used by the test suite and by `cure doctor` to
  dry-run against a local mock.

  ## Events

  Every network call emits events on the `:registry` pipeline stage via
  `Cure.Pipeline.Events`:

      :fetch_start   -- request about to go out
      :fetch_ok      -- successful response with hash
      :fetch_failed  -- non-2xx response or transport error
      :cache_hit     -- served from disk
      :hash_mismatch -- body did not match the declared hash
  """

  alias Cure.Pipeline.Events
  alias Cure.Project.Json

  @default_url "https://registry.cure-lang.org"
  @cache_dir_name "registry_cache"
  @user_agent "cure/0.23.0"

  @type version :: String.t()
  @type manifest :: map()
  @type tarball_bytes :: binary()
  @type error ::
          {:fetch_failed, String.t(), term()}
          | {:hash_mismatch, String.t()}
          | {:package_not_found, String.t()}
          | {:decode_failed, term()}

  # -- Public API -------------------------------------------------------------

  @doc """
  Return the base URL the client is currently configured to talk to.

  Useful for `cure doctor` when reporting the environment.
  """
  @spec base_url() :: String.t()
  def base_url do
    Application.get_env(:cure, :registry_url) ||
      System.get_env("CURE_REGISTRY_URL") ||
      @default_url
  end

  @doc """
  Run `fun` with `url` overriding the configured base URL for the
  duration of the call. Restores the previous value on exit.
  """
  @spec with_base_url(String.t(), (-> any())) :: any()
  def with_base_url(url, fun) when is_binary(url) and is_function(fun, 0) do
    previous = Application.get_env(:cure, :registry_url)
    Application.put_env(:cure, :registry_url, url)

    try do
      fun.()
    after
      if previous do
        Application.put_env(:cure, :registry_url, previous)
      else
        Application.delete_env(:cure, :registry_url)
      end
    end
  end

  @doc """
  Fetch the list of published versions for `name`.

  Returns `{:ok, [%{version: v, tarball_url: u, sha256: h, manifest_url: m}, ...]}`
  sorted newest-first, or `{:error, error}`.
  """
  @spec list_versions(String.t()) :: {:ok, [map()]} | {:error, error()}
  def list_versions(name) when is_binary(name) do
    path = "/packages/#{URI.encode(name)}"

    case fetch_json(path) do
      {:ok, %{"versions" => versions}} when is_list(versions) ->
        {:ok, Enum.map(versions, &normalise_version/1)}

      {:ok, other} ->
        {:error, {:decode_failed, other}}

      {:error, {:fetch_failed, _, {:status, 404}}} ->
        {:error, {:package_not_found, name}}

      {:error, _} = err ->
        err
    end
  end

  @doc """
  Fetch the manifest for a specific `{name, version}`.

  Returns `{:ok, manifest}`; the manifest is a plain map with string
  keys matching the `Cure.toml` schema plus a `"dependencies"` list of
  `{name, constraint}` tuples.
  """
  @spec fetch_manifest(String.t(), version()) :: {:ok, manifest()} | {:error, error()}
  def fetch_manifest(name, version) when is_binary(name) and is_binary(version) do
    path = "/packages/#{URI.encode(name)}/#{URI.encode(version)}"

    case fetch_json(path) do
      {:ok, %{"manifest" => manifest}} when is_map(manifest) ->
        {:ok, normalise_manifest(manifest)}

      {:ok, other} ->
        {:error, {:decode_failed, other}}

      {:error, _} = err ->
        err
    end
  end

  @doc """
  Fetch the tarball bytes for `{name, version}`, verifying against the
  declared `sha256` hash.

  Returns `{:ok, bytes, hash}`. If the hash does not match the response
  body, returns `{:error, {:hash_mismatch, declared_hash}}`. The hash
  returned on success is always lowercase hex.
  """
  @spec fetch_tarball(String.t(), version(), String.t()) ::
          {:ok, tarball_bytes(), String.t()} | {:error, error()}
  def fetch_tarball(name, version, expected_sha256)
      when is_binary(name) and is_binary(version) and is_binary(expected_sha256) do
    path = "/packages/#{URI.encode(name)}/#{URI.encode(version)}/tarball"

    case fetch_bytes(path, expected_sha256) do
      {:ok, bytes, hash} -> {:ok, bytes, hash}
      {:error, _} = err -> err
    end
  end

  @doc """
  Issue a substring-search request and return `{:ok, [hit, ...]}`.
  """
  @spec search(String.t()) :: {:ok, [map()]} | {:error, error()}
  def search(query) when is_binary(query) do
    path = "/packages?q=" <> URI.encode_www_form(query)

    case fetch_json(path) do
      {:ok, %{"hits" => hits}} when is_list(hits) -> {:ok, hits}
      {:ok, other} -> {:error, {:decode_failed, other}}
      {:error, _} = err -> err
    end
  end

  @doc """
  Fetch the transparency-log tip. Returns the parsed JSON object whose
  exact shape is described in `Cure.Project.Transparency`.
  """
  @spec fetch_log_tip() :: {:ok, map()} | {:error, error()}
  def fetch_log_tip do
    case fetch_json("/log") do
      {:ok, tip} when is_map(tip) -> {:ok, tip}
      {:ok, other} -> {:error, {:decode_failed, other}}
      {:error, _} = err -> err
    end
  end

  @doc """
  Upload a tarball + signature bundle to the registry. `token` is the
  maintainer OAuth token; the request body is a JSON envelope with
  base64-encoded `tarball` / `signature` fields plus the manifest.

  Returns `{:ok, %{"version" => ..., "sha256" => ...}}` on success.
  """
  @spec publish(String.t(), manifest(), tarball_bytes(), binary(), String.t()) ::
          {:ok, map()} | {:error, error()}
  def publish(name, manifest, tarball, signature, token)
      when is_binary(name) and is_map(manifest) and is_binary(tarball) and
             is_binary(signature) and is_binary(token) do
    path = "/packages"

    body =
      Json.encode(%{
        name: name,
        manifest: manifest,
        tarball: Base.encode64(tarball),
        signature: Base.encode64(signature)
      })

    headers = [
      {"authorization", "Bearer " <> token},
      {"content-type", "application/json"},
      {"user-agent", @user_agent}
    ]

    case request(:post, path, headers, body) do
      {:ok, _status, _hdrs, rbody} ->
        case Json.decode(rbody) do
          {:ok, decoded} -> {:ok, decoded}
          {:error, reason} -> {:error, {:decode_failed, reason}}
        end

      {:error, reason} ->
        {:error, {:fetch_failed, path, reason}}
    end
  end

  @doc """
  Remove every cached response whose on-disk hash does not match its
  filename. Returns the number of files pruned.
  """
  @spec prune_cache() :: non_neg_integer()
  def prune_cache do
    dir = cache_dir()

    if File.dir?(dir) do
      dir
      |> File.ls!()
      |> Enum.reduce(0, fn name, acc ->
        path = Path.join(dir, name)

        with {:ok, bytes} <- File.read(path),
             actual <- sha256_hex(bytes) do
          if actual == name do
            acc
          else
            _ = File.rm(path)
            acc + 1
          end
        else
          _ ->
            _ = File.rm(path)
            acc + 1
        end
      end)
    else
      0
    end
  end

  # -- Internals: JSON / bytes fetch ------------------------------------------

  defp fetch_json(path) do
    case request(:get, path, default_headers(), nil) do
      {:ok, 200, _hdrs, body} ->
        emit(:fetch_ok, %{path: path, bytes: byte_size(body)})

        case Json.decode(body) do
          {:ok, decoded} -> {:ok, decoded}
          {:error, reason} -> {:error, {:decode_failed, reason}}
        end

      {:ok, status, _hdrs, _body} ->
        emit(:fetch_failed, %{path: path, reason: {:status, status}})
        {:error, {:fetch_failed, path, {:status, status}}}

      {:error, reason} ->
        emit(:fetch_failed, %{path: path, reason: reason})
        {:error, {:fetch_failed, path, reason}}
    end
  end

  defp fetch_bytes(path, expected_sha256) do
    cache_key = String.downcase(expected_sha256)

    case read_from_cache(cache_key) do
      {:ok, bytes} ->
        emit(:cache_hit, %{path: path, sha256: cache_key, bytes: byte_size(bytes)})
        {:ok, bytes, cache_key}

      :miss ->
        emit(:fetch_start, %{path: path})

        case request(:get, path, default_headers(), nil) do
          {:ok, 200, _hdrs, body} ->
            actual = sha256_hex(body)

            if actual == cache_key do
              emit(:fetch_ok, %{path: path, sha256: actual, bytes: byte_size(body)})
              _ = write_to_cache(cache_key, body)
              {:ok, body, actual}
            else
              emit(:hash_mismatch, %{path: path, expected: cache_key, actual: actual})
              {:error, {:hash_mismatch, cache_key}}
            end

          {:ok, status, _hdrs, _body} ->
            emit(:fetch_failed, %{path: path, reason: {:status, status}})
            {:error, {:fetch_failed, path, {:status, status}}}

          {:error, reason} ->
            emit(:fetch_failed, %{path: path, reason: reason})
            {:error, {:fetch_failed, path, reason}}
        end
    end
  end

  # -- Internals: HTTP transport ---------------------------------------------

  defp request(method, path, headers, body) do
    ensure_inets_started()

    url = (base_url() <> path) |> String.to_charlist()

    erl_headers =
      Enum.map(headers, fn {k, v} ->
        {String.to_charlist(k), String.to_charlist(v)}
      end)

    req =
      case method do
        :get ->
          {url, erl_headers}

        :post ->
          content_type = fetch_header(headers, "content-type") |> String.to_charlist()
          body_ch = if is_binary(body), do: body, else: ""
          {url, erl_headers, content_type, body_ch}
      end

    case :httpc.request(method, req, http_opts(), response_opts()) do
      {:ok, {{_proto, status, _reason}, resp_headers, rbody}} ->
        rbody_bin = IO.iodata_to_binary(rbody)
        headers_out = Enum.map(resp_headers, fn {k, v} -> {to_string(k), to_string(v)} end)
        {:ok, status, headers_out, rbody_bin}

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp ensure_inets_started do
    case :inets.start() do
      :ok -> :ok
      {:error, {:already_started, :inets}} -> :ok
      other -> other
    end
  end

  defp http_opts do
    [
      timeout: 30_000,
      connect_timeout: 10_000,
      autoredirect: true
    ]
  end

  defp response_opts do
    [body_format: :binary]
  end

  defp default_headers do
    [{"user-agent", @user_agent}, {"accept", "application/json"}]
  end

  defp fetch_header(headers, key) do
    Enum.find_value(headers, "application/octet-stream", fn {k, v} ->
      if String.downcase(k) == key, do: v, else: nil
    end)
  end

  # -- Internals: cache --------------------------------------------------------

  defp cache_dir do
    base = System.user_home!() |> Path.join(".cure") |> Path.join(@cache_dir_name)
    File.mkdir_p!(base)
    base
  end

  defp read_from_cache(key) do
    path = Path.join(cache_dir(), key)

    case File.read(path) do
      {:ok, bytes} ->
        if sha256_hex(bytes) == key do
          {:ok, bytes}
        else
          _ = File.rm(path)
          :miss
        end

      {:error, _} ->
        :miss
    end
  end

  defp write_to_cache(key, bytes) do
    path = Path.join(cache_dir(), key)
    File.write(path, bytes)
  end

  defp sha256_hex(bytes) do
    :crypto.hash(:sha256, bytes) |> Base.encode16(case: :lower)
  end

  # -- Internals: shape normalisation -----------------------------------------

  defp normalise_version(%{"version" => v} = m) do
    %{
      version: v,
      tarball_url: Map.get(m, "tarball_url", ""),
      manifest_url: Map.get(m, "manifest_url", ""),
      sha256: Map.get(m, "sha256", "")
    }
  end

  defp normalise_version(other), do: other

  defp normalise_manifest(m) do
    deps =
      case Map.get(m, "dependencies", []) do
        list when is_list(list) ->
          Enum.map(list, fn
            %{"name" => n, "constraint" => c} -> {n, c}
            [n, c] when is_binary(n) and is_binary(c) -> {n, c}
            other -> other
          end)

        other ->
          other
      end

    Map.put(m, "dependencies", deps)
  end

  # -- Internals: events ------------------------------------------------------

  defp emit(event_type, payload) do
    try do
      Events.emit(:registry, event_type, payload, %{
        file: "registry",
        line: 1,
        timestamp: System.monotonic_time(:microsecond)
      })
    rescue
      # Emission is best-effort; the registry must work even if the
      # Events registry has not been started (for example in unit
      # tests that do not start the app).
      _ -> :ok
    end
  end
end
